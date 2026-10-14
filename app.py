import os
import json
import math
from flask import Flask, abort, g, render_template, request, redirect, url_for, session, flash, jsonify, has_app_context
from flask_sqlalchemy import SQLAlchemy
from werkzeug.utils import secure_filename
from sqlalchemy import inspect, text, func, Integer, String, or_, and_
from sqlalchemy.exc import IntegrityError
from datetime import datetime, timedelta, timezone
import calendar
import re
from urllib.parse import urlparse
from types import SimpleNamespace
import flask_migrate
import traceback



app = Flask(__name__)


@app.template_filter('pakistan_time')
def pakistan_time(value):
    if value is None:
        return ''
    utc_value = value.replace(tzinfo=timezone.utc) if value.tzinfo is None else value.astimezone(timezone.utc)
    return utc_value.astimezone(timezone(timedelta(hours=5), name='PKT'))


app.config["SECRET_KEY"] = os.environ.get(
    "SECRET_KEY",
    "change-this-secret"
)

# Database Config
uri = os.environ.get('DATABASE_URL')

if uri:
    # Agar Render par PostgreSQL mil jaye
    if uri.startswith("postgres://"):
        uri = uri.replace("postgres://", "postgresql://", 1)
    app.config['SQLALCHEMY_DATABASE_URI'] = uri
else:
    # Use the Railway volume path in production, and the project folder locally.
    basedir = os.path.abspath(os.path.dirname(__file__))
    sqlite_path = os.environ.get('SQLITE_DB_PATH',os.path.join(basedir, 'canon.db'))
    app.config['SQLALCHEMY_DATABASE_URI'] = 'sqlite:///' +os.path.abspath(sqlite_path)

app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False
app.config['UPLOAD_FOLDER'] = os.path.join(app.root_path, 'static', 'uploads')
os.makedirs(app.config['UPLOAD_FOLDER'], exist_ok=True)

db = SQLAlchemy(app)
print("SQLAlchemy initialized")





def parse_numeric(value):
    try:
        return float(str(value).replace(',', '').strip())
    except (ValueError, TypeError):
        return 0.0


def calculate_vendor_unit_rate(pack_qty, pack_price):
    pack_qty_value = parse_numeric(pack_qty)
    pack_price_value = parse_numeric(pack_price)
    if pack_qty_value > 0:
        return round(pack_price_value / pack_qty_value, 4) if pack_price_value else 0.0
    return pack_price_value


def is_roll_unit(unit):
    return (unit or '').strip().casefold() in {'roll', 'rolls'}


PACKAGE_UNITS = {
    'pack', 'packs', 'packet', 'packets', 'bundle', 'bundles', 'box', 'boxes',
    'carton', 'cartons', 'case', 'cases', 'bale', 'bales', 'bag', 'bags',
}


def is_package_unit(unit):
    return (unit or '').strip().casefold() in PACKAGE_UNITS


def unit_measure(unit):
    unit_key = (unit or '').strip().casefold()
    units = {
        'length': {
            'm': 1.0, 'meter': 1.0, 'meters': 1.0, 'metre': 1.0, 'metres': 1.0,
            'cm': 0.01, 'centimeter': 0.01, 'centimeters': 0.01,
            'mm': 0.001, 'millimeter': 0.001, 'millimeters': 0.001,
            'in': 0.0254, 'inch': 0.0254, 'inches': 0.0254,
            'ft': 0.3048, 'foot': 0.3048, 'feet': 0.3048,
            'yd': 0.9144, 'yard': 0.9144, 'yards': 0.9144,
            'km': 1000.0, 'kilometer': 1000.0, 'kilometers': 1000.0,
        },
        'count': {
            'pc': 1.0, 'pcs': 1.0, 'piece': 1.0, 'pieces': 1.0,
            'pair': 2.0, 'pairs': 2.0, 'dozen': 12.0, 'doz': 12.0, 'dz': 12.0,
            'gross': 144.0,
        },
        'mass': {
            'kg': 1.0, 'kilogram': 1.0, 'kilograms': 1.0,
            'g': 0.001, 'gm': 0.001, 'gram': 0.001, 'grams': 0.001,
            'mg': 0.000001, 'milligram': 0.000001, 'milligrams': 0.000001,
            'lb': 0.45359237, 'lbs': 0.45359237, 'pound': 0.45359237,
            'oz': 0.028349523125, 'ounce': 0.028349523125, 'ounces': 0.028349523125,
        },
        'volume': {
            'l': 1.0, 'liter': 1.0, 'liters': 1.0, 'litre': 1.0, 'litres': 1.0,
            'ml': 0.001, 'milliliter': 0.001, 'milliliters': 0.001,
            'millilitre': 0.001, 'millilitres': 0.001,
        },
    }
    for dimension, factors in units.items():
        if unit_key in factors:
            return dimension, factors[unit_key]
    return None


def unit_conversion_factor(stock_unit, issue_unit):
    stock_key = (stock_unit or '').strip().casefold()
    issue_key = (issue_unit or '').strip().casefold()
    if stock_key == issue_key:
        return 1.0
    stock_measure = unit_measure(stock_key)
    issue_measure = unit_measure(issue_key)
    if stock_measure and issue_measure and stock_measure[0] == issue_measure[0]:
        return issue_measure[1] / stock_measure[1]
    return None


def is_discrete_issue_unit(unit):
    unit_key = (unit or '').strip().casefold()
    if not unit_key:
        return False
    measure = unit_measure(unit_key)
    return measure is None or measure[0] == 'count'


def round_accessory_qty_to_issue_unit(item, quantity):
    issue_unit = item.issue_unit or item.unit or ''
    factor = parse_numeric(item.issue_unit_factor)
    if not is_discrete_issue_unit(issue_unit) or factor <= 0:
        return quantity
    return math.ceil(quantity / factor - 1e-10) * factor


def accessory_issue_stock_qty(item, issue_qty, issue_unit=None):
    selected_unit = (issue_unit or item.issue_unit or item.unit or '').strip().casefold()
    stock_unit = (item.unit or '').strip().casefold()
    factor = parse_numeric(item.issue_unit_factor) or 1.0
    if selected_unit == stock_unit:
        return parse_numeric(issue_qty)
    return parse_numeric(issue_qty) * factor


def default_issue_unit_for_item(item_name, fallback_unit='PCS'):
    item_name = (item_name or '').strip()
    if not item_name:
        return (fallback_unit or 'PCS').strip() or 'PCS'

    if not has_app_context():
        return (fallback_unit or 'PCS').strip() or 'PCS'

    master_item = ItemMaster.query.filter(
        func.lower(func.trim(ItemMaster.item_name)) == item_name.casefold()
    ).first()
    if master_item:
        preferred_unit = (master_item.issue_unit or master_item.unit or fallback_unit or 'PCS').strip()
        return preferred_unit or (fallback_unit or 'PCS')
    return (fallback_unit or 'PCS').strip() or 'PCS'


def accessory_usage_stock_qty(item, usage_qty, usage_unit):
    usage_unit = (usage_unit or '').strip().casefold()
    stock_unit = (item.unit or '').strip().casefold()
    conversion_factor = unit_conversion_factor(stock_unit, usage_unit)
    if conversion_factor is not None:
        return parse_numeric(usage_qty) * conversion_factor
    issue_unit = (item.issue_unit or '').strip().casefold()
    issue_conversion_factor = parse_numeric(item.issue_unit_factor)
    conversion_factor = unit_conversion_factor(issue_unit, usage_unit)
    if conversion_factor is not None and issue_conversion_factor > 0:
        return parse_numeric(usage_qty) * conversion_factor * issue_conversion_factor
    if usage_unit == stock_unit:
        return parse_numeric(usage_qty)
    if usage_unit == issue_unit:
        return parse_numeric(usage_qty) * (issue_conversion_factor or 1.0)
    usage_meters = length_to_meters(usage_qty, usage_unit)
    if usage_meters > 0 and is_roll_unit(stock_unit) and parse_numeric(item.roll_length_m) > 0:
        return usage_meters / parse_numeric(item.roll_length_m)
    return 0.0


def is_whole_stock_quantity(item, quantity):
    return not is_discrete_issue_unit(item.unit) or abs(quantity - round(quantity)) <= 0.000001


def length_to_meters(quantity, unit):
    measure = unit_measure(unit)
    return parse_numeric(quantity) * measure[1] if measure and measure[0] == 'length' else 0.0


def required_roll_quantity(order_pcs, usage_per_piece, usage_unit, meters_per_roll):
    length_required = length_to_meters(order_pcs * usage_per_piece, usage_unit)
    roll_length = parse_numeric(meters_per_roll)
    if length_required <= 0 or roll_length <= 0:
        return 0
    return math.ceil(length_required / roll_length - 1e-10)


def find_lowest_cost_vendor(article_specs, order_qty):
    required_specs = [spec for spec in article_specs[:6] if (spec.item_name or '').strip()]
    if not required_specs:
        return ''

    vendor_costs = []
    for vendor in Vendor.query.order_by(Vendor.name.asc()).all():
        vendor_items_by_name = {}
        for vendor_item in vendor.items:
            item_name = (vendor_item.item_name or '').strip().casefold()
            if not item_name:
                continue
            vendor_items_by_name.setdefault(item_name, []).append(vendor_item)

        total_cost = 0.0
        covers_all_items = True
        for spec in required_specs:
            item_name = (spec.item_name or '').strip().casefold()
            if item_name not in vendor_items_by_name:
                covers_all_items = False
                break
            master_item = ItemMaster.query.filter(
                func.lower(func.trim(ItemMaster.item_name)) == item_name
            ).first()
            quantity_per_piece = parse_numeric(spec.qty_per_piece)
            required_meters = length_to_meters(
                parse_numeric(order_qty) * quantity_per_piece, spec.unit
            )
            if required_meters > 0:
                option_costs = []
                for vendor_item in vendor_items_by_name[item_name]:
                    if is_roll_unit(vendor_item.unit):
                        meters_per_roll = length_to_meters(vendor_item.pack_qty, 'METER')
                        pack_price = parse_numeric(vendor_item.pack_price) or parse_numeric(vendor_item.rate)
                        if meters_per_roll > 0 and pack_price > 0:
                            option_costs.append(required_meters * pack_price / meters_per_roll)
                        continue
                    meters_per_unit = length_to_meters(1, vendor_item.unit)
                    unit_rate = parse_numeric(vendor_item.rate)
                    if meters_per_unit > 0 and unit_rate > 0:
                        option_costs.append(required_meters / meters_per_unit * unit_rate)
                if not option_costs:
                    covers_all_items = False
                    break
                total_cost += min(option_costs)
                continue
            package_options = []
            required_quantity = parse_numeric(order_qty) * quantity_per_piece
            for vendor_item in vendor_items_by_name[item_name]:
                if not is_package_unit(vendor_item.unit):
                    continue
                vendor_pack_qty = parse_numeric(vendor_item.pack_qty)
                vendor_rate = parse_numeric(vendor_item.rate)
                package_price = parse_numeric(vendor_item.pack_price) or (
                    vendor_rate * vendor_pack_qty if vendor_pack_qty > 0 else vendor_rate
                )
                if (spec.unit or '').strip().casefold() == (vendor_item.unit or '').strip().casefold() and package_price > 0:
                    package_options.append(required_quantity * package_price)
                elif vendor_item.pack_qty > 0 and package_price > 0:
                    package_options.append(
                        math.ceil(required_quantity / vendor_item.pack_qty - 1e-10) * package_price
                    )
            if package_options:
                total_cost += min(package_options)
                continue
            has_package_vendor_item = any(
                is_package_unit(vendor_item.unit)
                for vendor_item in vendor_items_by_name[item_name]
            )
            if is_package_unit(master_item.unit if master_item else '') or has_package_vendor_item:
                covers_all_items = False
                break
            roll_item = is_roll_unit(master_item.unit if master_item else '') or any(
                is_roll_unit(vendor_item.unit)
                for vendor_item in vendor_items_by_name[item_name]
            )
            if roll_item:
                option_costs = []
                for vendor_item in vendor_items_by_name[item_name]:
                    if not is_roll_unit(vendor_item.unit):
                        continue
                    roll_quantity = required_roll_quantity(
                        parse_numeric(order_qty), quantity_per_piece, spec.unit, vendor_item.pack_qty
                    )
                    roll_price = parse_numeric(vendor_item.pack_price) or parse_numeric(vendor_item.rate)
                    if roll_quantity > 0 and roll_price > 0:
                        option_costs.append(roll_quantity * roll_price)
                if not option_costs:
                    covers_all_items = False
                    break
                total_cost += min(option_costs)
            else:
                total_quantity = parse_numeric(order_qty) * quantity_per_piece
                item_rates = [parse_numeric(item.rate) for item in vendor_items_by_name[item_name]]
                valid_rates = [rate for rate in item_rates if rate > 0]
                if not valid_rates:
                    covers_all_items = False
                    break
                total_cost += total_quantity * min(valid_rates)

        if covers_all_items:
            vendor_costs.append((total_cost, vendor.name.casefold(), vendor.name))

    if not vendor_costs:
        return ''
    return min(vendor_costs)[2]


def save_order_images(order, uploaded_files):
    try:
        saved_images = json.loads(order.image_files or '[]')
        if not isinstance(saved_images, list):
            saved_images = []
    except (TypeError, ValueError):
        saved_images = []

    if order.image_file and order.image_file not in saved_images:
        saved_images.insert(0, order.image_file)

    allowed = {'png', 'jpg', 'jpeg', 'webp'}
    for image_index, image_file in enumerate(uploaded_files):
        if not image_file or not image_file.filename:
            continue
        extension = image_file.filename.lower().rsplit('.', 1)[-1]
        if extension not in allowed:
            continue
        filename = secure_filename(image_file.filename)
        filename = f"{datetime.utcnow().strftime('%Y%m%d%H%M%S%f')}_{filename}"
        image_file.save(os.path.join(app.config['UPLOAD_FOLDER'], filename))
        image_path = f"/static/uploads/{filename}"
        if image_index < len(saved_images):
            saved_images[image_index] = image_path
        else:
            saved_images.append(image_path)

    order.image_files = json.dumps(saved_images)
    if saved_images and not order.image_file:
        order.image_file = saved_images[0]
    return saved_images


def split_inventory_serials(value):
    raw_value = (value or '').strip()
    if not raw_value:
        return []
    if '-' not in raw_value or '/' not in raw_value:
        return [raw_value]
    number_part, year_part = raw_value.rsplit('/', 1)
    return [f'{part}/{year_part}' for part in number_part.split('-') if part]


def inventory_b_activation_cut(inventory_obj, order_id=None):
    activation_cut_no = getattr(inventory_obj, 'fabric_b_activation_cut_no', None)
    activation_order_id = getattr(inventory_obj, 'fabric_b_activation_order_id', None)
    if order_id and order_id == getattr(inventory_obj, 'order_id', None) and not activation_order_id:
        existing_cut_numbers = []
        for sheet in CuttingSheet.query.filter_by(order_id=order_id).all():
            if inventory_obj.serial_no not in split_inventory_serials(sheet.inventory_serial_no):
                continue
            try:
                existing_cut_numbers.append(int(str(sheet.cut_no)))
            except (TypeError, ValueError):
                continue
        if existing_cut_numbers:
            return max(existing_cut_numbers) + 1
        return 1
    return activation_cut_no


def inventory_b_active_for_cut(inventory_obj, cut_no, order_id=None):
    if not inventory_obj or not getattr(inventory_obj, 'fabric_b_enabled', False):
        return False
    activation_cut_no = inventory_b_activation_cut(inventory_obj, order_id)
    try:
        return activation_cut_no is not None and int(cut_no) >= int(activation_cut_no)
    except (TypeError, ValueError):
        return False


def calculate_inventory_b_quality_remaining(inventory_obj, order_id=None):
    if not inventory_obj or not getattr(inventory_obj, 'fabric_b_enabled', False):
        return 0.0
    return calculate_inventory_consumption_state(
        inventory_obj,
        order_id=order_id,
    )['b_remaining']


def calculate_inventory_returnable_a_quantity(inventory_obj, order_id=None):
    if not inventory_obj:
        return 0.0
    return max(0.0, calculate_inventory_consumption_state(
        inventory_obj,
        order_id=order_id,
    )['a_remaining'])


def calculate_inventory_returnable_b_quantity(inventory_obj, order_id=None):
    if not inventory_obj:
        return 0.0

    if getattr(inventory_obj, 'fabric_b_enabled', False):
        return calculate_inventory_b_quality_remaining(inventory_obj, order_id=order_id)

    fallback_b = max(0.0, parse_numeric(getattr(inventory_obj, 'fabric_qty_b', 0)))
    if fallback_b <= 0:
        return 0.0

    if getattr(inventory_obj, 'id', None) is None:
        return fallback_b

    simulated = SimpleNamespace(**vars(inventory_obj))
    simulated.fabric_b_enabled = True
    remaining_b = calculate_inventory_b_quality_remaining(simulated, order_id=order_id)
    return remaining_b if remaining_b > 0 else fallback_b


def calculate_inventory_used_fabric(serial_no, order_id=None):
    if not serial_no:
        return 0.0
    if order_id is None:
        order_id = ''

    related_order_ids = None
    if order_id:
        current_order = Order.query.filter_by(job_no=order_id).first()
        if current_order:
            article_filters = [
                func.lower(Order.article) == func.lower(current_order.article),
                func.lower(Order.article) == func.lower(display_article_no(current_order.article)),
            ]
            if current_order.article_id:
                article_filters.insert(0, Order.article_id == current_order.article_id)
            related_order_ids = {
                linked_order.job_no
                for linked_order in Order.query.filter(or_(*article_filters)).all()
                if linked_order.job_no
            }
            related_order_ids.add(order_id)

    order_inventories = (
        Inventory.query.filter(Inventory.order_id.in_(related_order_ids)).all()
        if related_order_ids
        else Inventory.query.all()
    )
    balances = {}
    used_map = {}
    b_added = set()

    for inv in order_inventories:
        if not inv.serial_no:
            continue
        total_received = parse_numeric(getattr(inv, 'fabric_qty_a', 0))
        rejected_value = max(0.0, parse_numeric(getattr(inv, 'rejected_fabric', 0)))
        reactive_value = max(0.0, parse_numeric(getattr(inv, 'rejected_recovered_fabric', 0)))
        normal_balance = max(0.0, total_received - rejected_value - reactive_value)
        balances[inv.serial_no] = normal_balance + reactive_value
        used_map[inv.serial_no] = 0.0

    sheets = (
        CuttingSheet.query.filter(CuttingSheet.order_id.in_(related_order_ids)).all()
        if related_order_ids
        else CuttingSheet.query.all()
    )
    sheets = sorted(
        sheets,
        key=lambda sheet: (
            int(str(sheet.cut_no)) if str(sheet.cut_no).strip().isdigit() else 999999,
            sheet.id or 0
        )
    )

    for sheet in sheets:
        try:
            sheet_cut_no = int(str(sheet.cut_no))
        except (TypeError, ValueError):
            sheet_cut_no = 0
        for inv in order_inventories:
            if inv.serial_no in b_added:
                continue
            if inventory_b_active_for_cut(inv, sheet_cut_no, sheet.order_id):
                balances[inv.serial_no] = balances.get(inv.serial_no, 0.0) + parse_numeric(inv.fabric_qty_b)
                b_added.add(inv.serial_no)
        sheet_serials = split_inventory_serials(sheet.inventory_serial_no)
        if not sheet_serials:
            continue

        try:
            remaining_usage = float(sheet.total_meter or 0)
        except (TypeError, ValueError):
            continue

        for sheet_serial in sheet_serials:
            if remaining_usage <= 0:
                break
            if sheet_serial not in balances:
                continue

            available = max(0.0, balances.get(sheet_serial, 0.0))
            allocated = min(available, remaining_usage)
            if allocated > 0:
                balances[sheet_serial] = available - allocated
                used_map[sheet_serial] = used_map.get(sheet_serial, 0.0) + allocated
                remaining_usage -= allocated

    return used_map.get(serial_no, 0.0)


def recalculate_all_inventory_balances():
    inventories = Inventory.query.all()
    for inv in inventories:
        if not inv.serial_no:
            continue
        actual_used = calculate_inventory_actual_used_fabric(inv)
        status = calculate_inventory_fabric_balances(inv)
        inv.used_fabric = f"{actual_used:.2f}"
        inv.left_over_fabric = f"{max(0.0, status['left_over_fabric']):.2f}"
        inv.rejected_fabric = f"{status['rejected_fabric']:.2f}"
    db.session.commit()


def calculate_inventory_actual_used_fabric(inventory_obj):
    if not inventory_obj or not getattr(inventory_obj, 'id', None):
        return 0.0
    return sum(
        parse_numeric(row.fabric_use)
        for row in InventoryRow.query.filter_by(inventory_id=inventory_obj.id).all()
        if row.fabric_use not in (None, '')
    )


def get_inventory_status(inventory_obj):
    if not inventory_obj:
        return 'Not Used'

    actual_used = calculate_inventory_actual_used_fabric(inventory_obj)
    balance = calculate_inventory_fabric_balances(inventory_obj)
    rejected_fabric = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_fabric', 0)))
    received_total = parse_numeric(getattr(inventory_obj, 'total', 0))
    if received_total <= 0:
        received_total = (
            parse_numeric(getattr(inventory_obj, 'fabric_qty_a', 0))
            + parse_numeric(getattr(inventory_obj, 'fabric_qty_b', 0))
            + parse_numeric(getattr(inventory_obj, 'b_returned_quantity', 0))
        )

    reactivated_remaining = balance['reactive_remaining']
    remaining_balance = balance['left_over_fabric']

    if actual_used <= 0:
        base_status = 'Not Used'
    elif actual_used > 0 and remaining_balance <= 0 and reactivated_remaining <= 0:
        base_status = 'Finished'
    elif received_total > 0 and actual_used >= received_total and reactivated_remaining > 0:
        base_status = 'Partially Used'
    else:
        inventory_order = Order.query.filter_by(job_no=inventory_obj.order_id).first()
        active_order_exists = False
        if inventory_order:
            article_order_numbers = get_article_order_numbers(inventory_order.job_no)
            relevant_orders = Order.query.filter(
                Order.job_no.in_(article_order_numbers),
                Order.id >= inventory_order.id,
            ).all()
            active_order_exists = any(
                (order.fulfillment_status or 'PENDING').strip().upper() != 'DELIVERED'
                for order in relevant_orders
            )
        base_status = 'Active' if active_order_exists else 'Partially Used'

    if rejected_fabric > 0:
        return f'{base_status} / Rejected'
    if reactivated_remaining > 0:
        return f'{base_status} / Re-active'
    return base_status


def calculate_inventory_consumption_state(inventory_obj, before_cut_no=None, order_id=None, before_date=None):
    """Replay inventory usage in cut order, respecting B activation timing."""
    if not inventory_obj:
        return {
            'a_remaining': 0.0,
            'b_remaining': 0.0,
            'reactive_remaining': 0.0,
            'used_fabric': 0.0,
        }

    rejected_remaining = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_fabric', 0)))
    reactive_remaining = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_recovered_fabric', 0)))
    a_remaining = max(
        0.0,
        parse_numeric(getattr(inventory_obj, 'fabric_qty_a', 0))
        - rejected_remaining
        - reactive_remaining,
    )
    b_remaining = (
        max(0.0, parse_numeric(getattr(inventory_obj, 'fabric_qty_b', 0)))
        if getattr(inventory_obj, 'fabric_b_enabled', False)
        else 0.0
    )
    used_fabric = 0.0
    effective_order_id = order_id or getattr(inventory_obj, 'order_id', None)
    current_file_no = None
    if order_id:
        current_order = Order.query.filter_by(job_no=order_id).first()
        current_file_no = (current_order.file_no or '').strip() if current_order else None
    rows = InventoryRow.query.filter_by(inventory_id=inventory_obj.id).all()
    rows.sort(key=lambda row: (
        int(str(row.cut_no)) if str(row.cut_no or '').strip().isdigit() else 999999,
        row.id or 0,
    ))

    for row in rows:
        try:
            row_cut_no = int(str(row.cut_no))
        except (TypeError, ValueError):
            row_cut_no = 0
        row_file_no = (row.file_no or '').strip()
        if before_date and row.date and str(row.date) > str(before_date):
            continue
        if (
            before_cut_no is not None
            and row_file_no == (current_file_no or '')
            and (not before_date or str(row.date or '') == str(before_date))
            and row_cut_no >= int(before_cut_no)
        ):
            continue

        usage_remaining = max(0.0, parse_numeric(row.fabric_use))
        used_fabric += usage_remaining
        used_from_a = min(a_remaining, usage_remaining)
        a_remaining -= used_from_a
        usage_remaining -= used_from_a

        if inventory_b_active_for_cut(inventory_obj, row_cut_no, effective_order_id):
            used_from_b = min(b_remaining, usage_remaining)
            b_remaining -= used_from_b
            usage_remaining -= used_from_b

        used_from_reactive = min(reactive_remaining, usage_remaining)
        reactive_remaining -= used_from_reactive

    return {
        'a_remaining': max(0.0, a_remaining),
        'b_remaining': max(0.0, b_remaining),
        'reactive_remaining': max(0.0, reactive_remaining),
        'used_fabric': used_fabric,
    }


def calculate_inventory_b_usage_for_period(inventory_obj, start_date=None, end_date=None, order_id=None):
    """Return B fabric meter and PCS consumed inside a selected date range.

    The meter is allocated to B only after A is exhausted for each cut in order, and the
    corresponding PCS is derived using the same ratio as the original cutting-sheet allocation.
    """
    if not inventory_obj or not getattr(inventory_obj, 'fabric_b_enabled', False):
        return {'meter': 0.0, 'pcs': 0.0}

    rejected_remaining = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_fabric', 0)))
    reactive_remaining = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_recovered_fabric', 0)))
    a_remaining = max(
        0.0,
        parse_numeric(getattr(inventory_obj, 'fabric_qty_a', 0))
        - rejected_remaining
        - reactive_remaining,
    )
    b_remaining = max(0.0, parse_numeric(getattr(inventory_obj, 'fabric_qty_b', 0)))
    effective_order_id = order_id or getattr(inventory_obj, 'order_id', None)
    used_meter = 0.0
    used_pcs = 0.0

    def row_cut_pcs_value(row, meter_used):
        if meter_used <= 0:
            return 0.0
        try:
            cut_no = str(row.cut_no or '').strip()
            sheet = CuttingSheet.query.filter_by(order_id=effective_order_id, cut_no=cut_no).order_by(CuttingSheet.id.desc()).first()
        except Exception:
            sheet = None
        total_meter = parse_numeric(getattr(sheet, 'total_meter', 0)) if sheet else 0.0
        total_pcs = (
            parse_numeric(getattr(sheet, 'quantity', 0))
            or parse_numeric(getattr(sheet, 'summary_total_pcs', 0))
            or parse_numeric(getattr(sheet, 'total_pcs', 0))
            or 0.0
        )
        if total_meter > 0 and total_pcs > 0:
            return (meter_used / total_meter) * total_pcs
        if row.cut_pcs not in (None, ''):
            return float(parse_numeric(row.cut_pcs))
        return 0.0

    rows = InventoryRow.query.filter_by(inventory_id=inventory_obj.id).all()
    rows.sort(key=lambda row: (
        int(str(row.cut_no)) if str(row.cut_no or '').strip().isdigit() else 999999,
        row.id or 0,
    ))

    for row in rows:
        row_usage = max(0.0, parse_numeric(row.fabric_use))
        if row_usage <= 0:
            continue

        row_date = normalize_date(row.date)
        in_period = (
            start_date is None or end_date is None
            or bool(row_date and start_date <= row_date.date() <= end_date)
        )

        usage_remaining = row_usage
        used_from_a = min(a_remaining, usage_remaining)
        a_remaining -= used_from_a
        usage_remaining -= used_from_a

        used_from_b = 0.0
        try:
            row_cut_no = int(str(row.cut_no))
        except (TypeError, ValueError):
            row_cut_no = 0
        if inventory_b_active_for_cut(inventory_obj, row_cut_no, effective_order_id):
            used_from_b = min(b_remaining, usage_remaining)
            b_remaining -= used_from_b
            usage_remaining -= used_from_b

        used_from_reactive = min(reactive_remaining, usage_remaining)
        reactive_remaining -= used_from_reactive

        if in_period:
            used_meter += used_from_b
            used_pcs += row_cut_pcs_value(row, used_from_b)

    return {'meter': used_meter, 'pcs': used_pcs}


def calculate_inventory_fabric_balances(inventory_obj):
    fabric_a = parse_numeric(getattr(inventory_obj, 'fabric_qty_a', 0))
    fabric_b = parse_numeric(getattr(inventory_obj, 'fabric_qty_b', 0)) if getattr(inventory_obj, 'fabric_b_enabled', False) else 0.0
    state = calculate_inventory_consumption_state(inventory_obj)
    raw_reactive_value = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_recovered_fabric', 0)))
    total_value = fabric_a + fabric_b
    left_over_value = max(
        0.0,
        state['a_remaining'] + state['b_remaining'] + state['reactive_remaining'],
    )

    return {
        'used_fabric': state['used_fabric'],
        'left_over_fabric': left_over_value,
        'rejected_fabric': max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_fabric', 0))),
        'recovered_fabric': raw_reactive_value,
        'reactive_remaining': state['reactive_remaining'],
        'remaining_b_quality': state['b_remaining'],
        'total_fabric': total_value,
    }


def calculate_inventory_reactive_fallback_pool(inventory_obj):
    if not inventory_obj or not getattr(inventory_obj, 'serial_no', None):
        return {
            'serial_no': '',
            'normal_balance': 0.0,
            'reactive_remaining': 0.0,
            'fallback_balance': 0.0,
            'active': False,
        }

    status = calculate_inventory_fabric_balances(inventory_obj)
    state = calculate_inventory_consumption_state(inventory_obj)
    rejected_value = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_fabric', 0)))
    raw_reactive_value = max(0.0, parse_numeric(getattr(inventory_obj, 'rejected_recovered_fabric', 0)))
    normal_balance = max(0.0, state['a_remaining'] + state['b_remaining'] - rejected_value)
    reactive_remaining = min(raw_reactive_value, state['reactive_remaining'])

    if reactive_remaining <= 0:
        return {
            'serial_no': inventory_obj.serial_no,
            'normal_balance': normal_balance,
            'reactive_remaining': 0.0,
            'fallback_balance': 0.0,
            'active': False,
        }

    threshold = max(0.0, normal_balance * 0.10)
    active = normal_balance <= threshold
    fallback_balance = normal_balance + reactive_remaining if active else 0.0
    return {
        'serial_no': inventory_obj.serial_no,
        'normal_balance': normal_balance,
        'reactive_remaining': reactive_remaining,
        'fallback_balance': fallback_balance,
        'active': active,
    }


def get_fabric_stock_totals():
    inventories = Inventory.query.filter(Inventory.serial_no.isnot(None)).all()
    totals = {'received': 0.0, 'issued': 0.0, 'balance': 0.0, 'rejected': 0.0}
    for inv in inventories:
        status = calculate_inventory_fabric_balances(inv)
        totals['received'] += status['total_fabric']
        totals['issued'] += status['used_fabric']
        totals['balance'] += status['left_over_fabric']
        totals['rejected'] += status['rejected_fabric']
    return totals


def is_party_supplied_stock_layer(item):
    return (item.serial_no or '').startswith('PARTY-SUPPLIED-')


def get_accessory_stock_summary():
    summary = {}
    for item in SavedRequirement.query.all():
        name = (item.item or 'UNSPECIFIED').strip().upper()
        bucket = summary.setdefault(name, {'ordered': 0.0, 'received': 0.0, 'issued': 0.0, 'used': 0.0, 'balance': 0.0})
        if not is_party_supplied_stock_layer(item):
            bucket['ordered'] += parse_numeric(item.qty)
        bucket['received'] += accessory_layer_received_qty(item)
        bucket['issued'] += accessory_layer_issued_qty(item)
        bucket['used'] += parse_numeric(item.used_qty)
        bucket['balance'] = bucket['received'] - bucket['issued']
    return summary


def accessory_stock_key(item_name, size='', quality='', unit='', roll_length_m=0):
    return tuple(
        (str(value or '').strip().casefold())
        for value in (item_name, size, quality, unit, f'{parse_numeric(roll_length_m):g}' if parse_numeric(roll_length_m) > 0 else '')
    )


def accessory_layer_received_qty(item):
    received = parse_numeric(item.received_qty)
    if received <= 0 and (item.accessory_status or '').upper() in {'RECEIVED', 'USED'}:
        received = parse_numeric(item.qty)
    return max(0.0, received)


def accessory_receipt_unit_rate(item):
    rate = parse_numeric(item.rate)
    if rate > 0:
        return rate
    quantity = parse_numeric(item.qty)
    amount = parse_numeric(item.bill_amount)
    return amount / quantity if quantity > 0 and amount > 0 else 0.0


def accessory_issue_returned_qty(issue):
    return sum(parse_numeric(entry.returned_qty) for entry in issue.return_entries)


def accessory_cut_pcs(cutting_sheet):
    row_pcs = sum(parse_numeric(row.pcs) for row in cutting_sheet.rows)
    return max(
        0.0,
        parse_numeric(cutting_sheet.total_pcs)
        or parse_numeric(cutting_sheet.summary_total_pcs)
        or parse_numeric(cutting_sheet.quantity)
        or row_pcs,
    )


def article_material_spec_for_item(order, item_name):
    if not order.article_id:
        return None
    return ArticleMaterialSpec.query.filter(
        ArticleMaterialSpec.article_id == order.article_id,
        func.lower(func.trim(ArticleMaterialSpec.item_name)) == (item_name or '').strip().casefold(),
    ).order_by(ArticleMaterialSpec.sort_order.asc(), ArticleMaterialSpec.id.asc()).first()


def accessory_required_qty_for_cut(item, order, cutting_pcs):
    if order.article_id:
        spec = article_material_spec_for_item(order, item.item)
        if spec:
            required_qty = accessory_usage_stock_qty(
                item, cutting_pcs * parse_numeric(spec.qty_per_piece), spec.unit
            )
            factor = parse_numeric(item.issue_unit_factor)
            if is_roll_unit(item.unit) and parse_numeric(item.roll_length_m) > 0:
                required_qty = math.ceil(required_qty - 1e-10)
            else:
                required_qty = round_accessory_qty_to_issue_unit(item, required_qty)
            if required_qty > 0:
                return required_qty
        return 0.0
    order_pcs = get_effective_order_quantity(order)
    return parse_numeric(item.qty) * cutting_pcs / order_pcs if order_pcs > 0 else 0.0


def build_cut_accessory_rows(order, cutting_sheet):
    cutting_pcs = accessory_cut_pcs(cutting_sheet)
    order_pcs = get_effective_order_quantity(order)
    groups = {}

    def get_group(item, size, quality, unit, sort_order, roll_length_m=0, issue_unit='', issue_unit_factor=1):
        display_unit = unit or ''
        key = tuple(
            (value or '').strip().casefold()
            for value in (item, size, quality, display_unit)
        )
        return groups.setdefault(key, {
            'item': item or 'UNSPECIFIED',
            'size': size or '',
            'quality': quality or '',
            'unit': display_unit,
            'required': 0.0,
            'issued': 0.0,
            'returned': 0.0,
            'net_issued': 0.0,
            'remaining': 0.0,
            'issued_to': [],
            'sort_order': sort_order,
        })

    specs = ArticleMaterialSpec.query.filter_by(article_id=order.article_id).order_by(
        ArticleMaterialSpec.sort_order.asc(), ArticleMaterialSpec.id.asc()
    ).all() if order.article_id else []
    order_issues = AccessoryIssue.query.filter_by(
        order_id=order.job_no,
    ).order_by(AccessoryIssue.id.asc()).all()
    cut_issues = AccessoryIssue.query.filter_by(
        order_id=order.job_no,
        cut_sheet_id=cutting_sheet.id,
    ).order_by(AccessoryIssue.id.asc()).all()
    if specs:
        for spec in specs:
            order_requirement = SavedRequirement.query.filter(
                SavedRequirement.order_id == order.job_no,
                func.lower(func.trim(SavedRequirement.item)) == (spec.item_name or '').strip().casefold(),
            ).order_by(SavedRequirement.id.asc()).first()
            spec_size = (spec.size or '').strip().casefold()
            spec_quality = (spec.material or '').strip().casefold()
            matching_issue_requirements = [
                issue.requirement for issue in order_issues
                if issue.requirement
                and (issue.requirement.item or '').strip().casefold() == (spec.item_name or '').strip().casefold()
                and (issue.requirement.size or '').strip().casefold() == spec_size
                and (issue.requirement.quality or '').strip().casefold() == spec_quality
            ]
            stock_requirement = next((
                requirement for requirement in matching_issue_requirements
                if accessory_layer_received_qty(requirement) > 0
            ), None)
            if not stock_requirement:
                matching_receipts = SavedRequirement.query.filter(
                    func.lower(func.trim(SavedRequirement.item)) == (spec.item_name or '').strip().casefold(),
                ).order_by(SavedRequirement.id.asc()).all()
                stock_requirement = next((
                    requirement for requirement in matching_receipts
                    if (requirement.size or '').strip().casefold() == spec_size
                    and (requirement.quality or '').strip().casefold() == spec_quality
                    and accessory_layer_received_qty(requirement) > 0
                ), None)
            if not stock_requirement:
                stock_requirement = order_requirement
            item_master = ItemMaster.query.filter(
                func.lower(func.trim(ItemMaster.item_name)) == (spec.item_name or '').strip().casefold()
            ).first()
            if stock_requirement:
                display_unit = (
                    (item_master.issue_unit or '').strip() if item_master else ''
                ) or stock_requirement.issue_unit or stock_requirement.unit
                group = get_group(
                    stock_requirement.item, stock_requirement.size, stock_requirement.quality,
                    display_unit, spec.sort_order or 0,
                )
                required_qty = accessory_usage_stock_qty(
                    stock_requirement, cutting_pcs * parse_numeric(spec.qty_per_piece), spec.unit
                )
                if is_roll_unit(stock_requirement.unit) and parse_numeric(stock_requirement.roll_length_m) > 0:
                    required_qty = math.ceil(required_qty - 1e-10)
                else:
                    required_qty = round_accessory_qty_to_issue_unit(stock_requirement, required_qty)
                normalized_display_unit = (display_unit or '').strip().casefold()
                normalized_stock_unit = (stock_requirement.unit or '').strip().casefold()
                normalized_receipt_issue_unit = (stock_requirement.issue_unit or '').strip().casefold()
                normalized_master_issue_unit = (
                    (item_master.issue_unit or '').strip().casefold() if item_master else ''
                )
                stock_per_issue_unit = 1.0
                if normalized_display_unit != normalized_stock_unit:
                    if normalized_display_unit == normalized_receipt_issue_unit:
                        stock_per_issue_unit = parse_numeric(stock_requirement.issue_unit_factor) or 1.0
                    elif normalized_display_unit == normalized_master_issue_unit and item_master:
                        stock_per_issue_unit = parse_numeric(item_master.issue_unit_factor) or 1.0
                    else:
                        stock_per_issue_unit = unit_conversion_factor(
                            stock_requirement.unit, display_unit
                        ) or 1.0
                group['required'] += required_qty / stock_per_issue_unit
                continue
            display_unit = (
                (item_master.issue_unit or '').strip() if item_master else ''
            ) or spec.unit
            group = get_group(
                spec.item_name,
                spec.size,
                spec.material,
                display_unit,
                spec.sort_order or 0,
            )
            required_qty = cutting_pcs * parse_numeric(spec.qty_per_piece)
            stock_per_issue_unit = (
                parse_numeric(item_master.issue_unit_factor) or 1.0
                if item_master and (display_unit or '').strip().casefold() != (spec.unit or '').strip().casefold()
                else 1.0
            )
            group['required'] += required_qty / stock_per_issue_unit
    elif order_pcs > 0 and not order.article_id:
        for requirement in SavedRequirement.query.filter_by(order_id=order.job_no).all():
            display_unit = requirement.issue_unit or requirement.unit
            group = get_group(
                requirement.item,
                requirement.size,
                requirement.quality,
                display_unit,
                999999,
            )
            required_qty = parse_numeric(requirement.qty) * cutting_pcs / order_pcs
            stock_per_issue_unit = (
                parse_numeric(requirement.issue_unit_factor) or 1.0
                if (display_unit or '').strip().casefold() != (requirement.unit or '').strip().casefold()
                else 1.0
            )
            group['required'] += required_qty / stock_per_issue_unit

    for issue in cut_issues:
        requirement = issue.requirement
        if not requirement:
            continue
        display_unit = issue.issued_as_unit or requirement.issue_unit or requirement.unit
        group = get_group(
            requirement.item,
            requirement.size,
            requirement.quality,
            display_unit,
            999999,
        )
        issued_qty = parse_numeric(issue.issued_qty)
        returned_qty = accessory_issue_returned_qty(issue)
        issue_conversion_factor = (
            parse_numeric(issue.issue_conversion_factor) or parse_numeric(requirement.issue_unit_factor) or 1.0
            if (display_unit or '').strip().casefold() != (requirement.unit or '').strip().casefold()
            else 1.0
        )
        entered_qty = parse_numeric(issue.issued_as_qty)
        issued_in_display_unit = (
            entered_qty
            if entered_qty > 0 and (issue.issued_as_unit or '').strip().casefold() == (display_unit or '').strip().casefold()
            else issued_qty / issue_conversion_factor
        )
        returned_in_display_unit = returned_qty / issue_conversion_factor
        worker_name = (issue.worker_name or '').strip()
        if worker_name:
            group['issued_to'] = list(dict.fromkeys(group['issued_to'] + [worker_name]))
        group['issued'] += issued_in_display_unit
        group['returned'] += returned_in_display_unit
        group['net_issued'] += max(0.0, issued_in_display_unit - returned_in_display_unit)

    result = list(groups.values())
    for group in result:
        group['remaining'] = max(0.0, group['required'] - group['net_issued'])
        group['issued_to_display'] = ', '.join(group['issued_to']) if group['issued_to'] else '—'
        group['display_unit'] = group['unit']
        group['display_required'] = group['required']
        group['display_net_issued'] = group['net_issued']
        group['display_remaining'] = group['remaining']
    result.sort(key=lambda row: (
        row['sort_order'],
        row['item'].casefold(),
        row['size'].casefold(),
    ))
    return result


def accessory_layer_issue_entries(item):
    issue_entries = list(item.issue_entries)
    received_at = (item.received_at or '').strip()
    if not received_at:
        return issue_entries

    try:
        received_date = datetime.strptime(received_at[:10], '%Y-%m-%d').date()
    except ValueError:
        return issue_entries

    return [
        issue for issue in issue_entries
        if issue.created_at is None or issue.created_at.date() >= received_date
    ]


def accessory_issue_net_qty(issue):
    return max(0.0, parse_numeric(issue.issued_qty) - accessory_issue_returned_qty(issue))


def accessory_layer_issued_qty(item):
    if item.issue_entries:
        return sum(accessory_issue_net_qty(issue) for issue in accessory_layer_issue_entries(item))
    return max(0.0, parse_numeric(item.issued_qty))


def is_accessory_returnable(item_name):
    item_name = (item_name or '').strip()
    if not item_name:
        return False
    item_master = ItemMaster.query.filter(
        func.lower(func.trim(ItemMaster.item_name)) == item_name.casefold()
    ).first()
    return bool(item_master and item_master.returnable)


def get_accessory_stock_positions():
    positions = {}
    receipt_rows = SavedRequirement.query.order_by(SavedRequirement.id.asc()).all()
    for item in receipt_rows:
        received_qty = accessory_layer_received_qty(item)
        if received_qty <= 0:
            continue
        issued_qty = accessory_layer_issued_qty(item)
        key = accessory_stock_key(item.item, item.size, item.quality, item.unit, item.roll_length_m)
        position = positions.setdefault(key, {
            'key': key,
            'item': item.item or 'UNSPECIFIED',
            'size': item.size or '',
            'quality': item.quality or '',
            'unit': item.unit or 'PCS',
            'issue_unit': item.issue_unit or item.unit or 'PCS',
            'issue_unit_factor': parse_numeric(item.issue_unit_factor) or 1.0,
            'roll_length_m': parse_numeric(item.roll_length_m),
            'received': 0.0,
            'issued': 0.0,
            'available': 0.0,
            'located': 0.0,
            'layers': [],
        })
        available_qty = max(0.0, received_qty - issued_qty)
        located_qty = sum(
            max(0.0, parse_numeric(location.quantity))
            for location in item.storage_locations
        )
        position['received'] += received_qty
        position['issued'] += issued_qty
        position['available'] += available_qty
        position['located'] += located_qty
        position['layers'].append({
            'requirement': item,
            'received': received_qty,
            'issued': issued_qty,
            'available': available_qty,
            'received_order': item.received_at or item.date or item.po_sent_at or '',
        })

    result = []
    for position in positions.values():
        position['layers'].sort(key=lambda layer: (
            layer['received_order'],
            layer['requirement'].id or 0,
        ))
        available_layers = [layer for layer in position['layers'] if layer['available'] > 0]
        anchor_layer = available_layers[0] if available_layers else position['layers'][0]
        position['anchor_id'] = anchor_layer['requirement'].id
        result.append(position)
    return sorted(result, key=lambda position: (
        position['item'].casefold(),
        position['size'].casefold(),
        position['quality'].casefold(),
        position['unit'].casefold(),
    ))


def accessory_storage_location_label(location):
    room = location.room or 'Store Room'
    department = (location.department or '').strip()
    if department:
        room = f'{department} · {room}'
    gala = (location.gala or '').strip()
    if gala:
        room = f'{room} · Gala {gala}'
    if location.location_type == 'RACK_SHELF':
        return f'{room} · Rack {location.rack_no} · Shelf {location.shelf_no}'
    if location.location_type == 'CARTON':
        label = f'{room} · Carton {location.carton_no}'
        if location.rack_no and location.shelf_no:
            label += f' (in front of Rack {location.rack_no} · Shelf {location.shelf_no})'
        return label
    if location.location_type == 'FLOOR':
        return f'{room} · Floor'
    if location.location_type in {'CABINET', 'CUPBOARD'}:
        return f'{room} · {location.location_type.title()}'
    return room


def accessory_storage_form_values(form):
    location_type = (form.get('location_type') or '').strip().upper()
    department = (form.get('department') or '').strip()
    gala = (form.get('gala') or '').strip()
    room = (form.get('room') or '').strip()
    rack_no = (form.get('rack_no') or '').strip()
    shelf_no = (form.get('shelf_no') or '').strip()
    carton_no = (form.get('carton_no') or '').strip()
    description = (form.get('description') or '').strip()
    quantity = parse_numeric(form.get('quantity'))

    if location_type not in {'RACK_SHELF', 'FLOOR', 'CABINET', 'CUPBOARD'}:
        raise ValueError('Choose a valid storage location type.')
    if not department or not Department.query.filter(
        func.lower(func.trim(Department.name)) == department.casefold()
    ).first():
        raise ValueError('Choose a valid department for this storage location.')
    if not room or not DepartmentStoreRoom.query.join(Department).filter(
        func.lower(func.trim(Department.name)) == department.casefold(),
        func.lower(func.trim(DepartmentStoreRoom.name)) == room.casefold(),
    ).first():
        raise ValueError('Choose a store room configured for the selected department.')
    if quantity <= 0:
        raise ValueError('Enter a storage quantity greater than zero.')
    if location_type == 'RACK_SHELF' and (not rack_no or not shelf_no):
        raise ValueError('Enter both the rack number and shelf number.')
    carton_no = ''
    if location_type != 'RACK_SHELF':
        rack_no = ''
        shelf_no = ''

    return {
        'location_type': location_type,
        'department': department,
        'gala': gala,
        'room': room,
        'rack_no': rack_no,
        'shelf_no': shelf_no,
        'carton_no': carton_no,
        'description': description,
        'quantity': quantity,
    }


def get_accessory_unlocated_qty(item):
    received_qty = accessory_layer_received_qty(item)
    issued_qty = accessory_layer_issued_qty(item)
    located_qty = sum(
        max(0.0, parse_numeric(location.quantity))
        for location in item.storage_locations
    )
    return max(0.0, received_qty - issued_qty - located_qty)


def get_accessory_storage_rows():
    rows = []
    for location in AccessoryStorageLocation.query.order_by(AccessoryStorageLocation.id.asc()).all():
        item = location.requirement
        if item is None:
            rows.append({
                'location': location,
                'item': f'Unlinked receipt #{location.requirement_id}',
                'size': '',
                'quality': '',
                'unit': '—',
                'roll_length_m': 0.0,
                'purchased': 0.0,
                'label': accessory_storage_location_label(location),
                'description': location.description or '',
                'po_no': '',
                'supplier': '',
                'orphaned': True,
            })
            continue
        rows.append({
            'location': location,
            'item': item.item or 'UNSPECIFIED',
            'size': item.size or '',
            'quality': item.quality or '',
            'unit': item.unit or 'PCS',
            'issue_unit': item.issue_unit or item.unit or 'PCS',
            'issue_unit_factor': parse_numeric(item.issue_unit_factor) or 1.0,
            'roll_length_m': parse_numeric(item.roll_length_m),
            'purchased': accessory_layer_received_qty(item),
            'label': accessory_storage_location_label(location),
            'description': location.description or '',
            'po_no': item.po_no or '',
            'supplier': item.supplier or '',
            'orphaned': False,
        })
    return rows


def accessory_history_normalized_quantity(item, quantity):
    quantity = parse_numeric(quantity)
    stock_unit = (item.unit or '').strip().casefold()
    stock_measure = unit_measure(stock_unit)
    canonical_units = {'length': 'METER', 'count': 'PCS', 'mass': 'KG', 'volume': 'LITER'}
    if stock_measure:
        return canonical_units[stock_measure[0]], quantity * stock_measure[1]
    if is_roll_unit(stock_unit) and parse_numeric(item.roll_length_m) > 0:
        return 'METER', quantity * parse_numeric(item.roll_length_m)

    issue_unit = (item.issue_unit or '').strip().casefold()
    conversion_factor = parse_numeric(item.issue_unit_factor)
    if issue_unit and issue_unit != stock_unit and conversion_factor > 0:
        issue_measure = unit_measure(issue_unit)
        if issue_measure:
            canonical_unit = canonical_units[issue_measure[0]]
            return canonical_unit, quantity / conversion_factor * issue_measure[1]
        return issue_unit.upper(), quantity / conversion_factor
    return (item.unit or 'PCS').strip().upper(), quantity


def get_accessory_received_history_groups(items):
    groups = {}
    for item in items:
        if item.received_value <= 0:
            continue

        display_unit, qty_value = accessory_history_normalized_quantity(item, item.qty_value)
        _, received_value = accessory_history_normalized_quantity(item, item.received_value)
        _, issued_value = accessory_history_normalized_quantity(item, item.issued_value)
        _, returned_value = accessory_history_normalized_quantity(item, item.returned_value)
        issue_unit = (item.issue_unit or item.unit or 'PCS').strip().upper()
        issue_factor = parse_numeric(item.issue_unit_factor) or 1.0
        stock_unit = (item.unit or 'PCS').strip().casefold()
        has_separate_issue_unit = issue_unit.casefold() != stock_unit
        key = tuple(
            (str(value or '').strip().casefold())
            for value in (item.item or 'UNSPECIFIED', item.size, item.quality)
        )
        group = groups.setdefault(key, {
            'id': item.id,
            'item': item.item or 'UNSPECIFIED',
            'variants': [],
            'unit_totals': {},
            'amounts': [],
            'orders': [],
            'suppliers': [],
            'purchase_slips': [],
            'issue_history_entries': [],
        })
        variant = (item.size or '', item.quality or '')
        if variant != ('', '') and variant not in group['variants']:
            group['variants'].append(variant)
        totals = group['unit_totals'].setdefault(display_unit, {
            'unit': display_unit,
            'qty_value': 0.0,
            'received_value': 0.0,
            'issued_value': 0.0,
            'returned_value': 0.0,
            'left_over_value': 0.0,
            'issue_unit_totals': {},
        })
        totals['qty_value'] += qty_value
        totals['received_value'] += received_value
        totals['issued_value'] += issued_value
        totals['returned_value'] += returned_value
        if has_separate_issue_unit:
            issue_totals = totals['issue_unit_totals'].setdefault(issue_unit, {
                'unit': issue_unit,
                'qty_value': 0.0,
                'received_value': 0.0,
                'issued_value': 0.0,
                'returned_value': 0.0,
                'left_over_value': 0.0,
            })
            issue_totals['qty_value'] += parse_numeric(item.qty_value) / issue_factor
            issue_totals['received_value'] += parse_numeric(item.received_value) / issue_factor
            issue_totals['issued_value'] += parse_numeric(item.issued_value) / issue_factor
            issue_totals['returned_value'] += parse_numeric(item.returned_value) / issue_factor

        order_label = 'LOCAL STOCK' if item.order_id == LOCAL_ACCESSORY_PO_ORDER_ID else (item.order_id or 'â€”')
        if order_label not in group['orders']:
            group['orders'].append(order_label)
        supplier = item.supplier or 'â€”'
        if supplier not in group['suppliers']:
            group['suppliers'].append(supplier)
        if item.purchase_slip_image and not any(
            slip['url'] == item.purchase_slip_image for slip in group['purchase_slips']
        ):
            group['purchase_slips'].append({
                'url': item.purchase_slip_image,
                'po_no': item.po_no or f'Requirement {item.id}',
            })
        for issue in item.issue_history_entries:
            group['issue_history_entries'].append(issue)

    result = list(groups.values())
    for group in result:
        group['amounts'] = sorted(group['unit_totals'].values(), key=lambda totals: totals['unit'].casefold())
        group['status_display'] = 'USED'
        for totals in group['amounts']:
            net_issued = max(0.0, totals['issued_value'] - totals['returned_value'])
            totals['left_over_value'] = max(0.0, totals['received_value'] - net_issued)
            totals['issue_amounts'] = sorted(totals.pop('issue_unit_totals').values(), key=lambda value: value['unit'].casefold())
            for issue_totals in totals['issue_amounts']:
                issue_net_issued = max(0.0, issue_totals['issued_value'] - issue_totals['returned_value'])
                issue_totals['left_over_value'] = max(0.0, issue_totals['received_value'] - issue_net_issued)
            if totals['left_over_value'] > 0.000001:
                group['status_display'] = 'RECEIVED'

    return sorted(result, key=lambda group: group['item'].casefold())


def get_order_production_progress(order):
    logs = ProductionLog.query.filter_by(job_no=order.job_no).all()
    operation_names = list(get_rates_for_order(order).keys())
    cutting_sheets = CuttingSheet.query.filter_by(order_id=order.job_no).all()
    final_operation_totals = []
    if cutting_sheets:
        for sheet in cutting_sheets:
            cut_operation_names = list(get_rates_for_cut(order, sheet.cut_no).keys())
            if not cut_operation_names:
                continue
            state = get_cut_production_state(
                order.job_no,
                sheet.cut_no,
                parse_numeric(sheet.quantity),
                cut_operation_names,
                logs=[log for log in logs if str(log.cut_no) == str(sheet.cut_no)],
            )
            final_operation_totals.append(
                state['credited_totals'].get(cut_operation_names[-1], 0)
            )
    if final_operation_totals or cutting_sheets:
        produced = sum(final_operation_totals)
    else:
        operation_totals = {}
        for log in logs:
            operation = (log.operation or 'OTHER').upper()
            operation_totals[operation] = operation_totals.get(operation, 0) + (log.pcs or 0)
        produced = operation_totals.get(
            operation_names[-1].upper(),
            max(operation_totals.values(), default=0),
        ) if operation_names else max(operation_totals.values(), default=0)
    ordered = get_effective_order_quantity(order)
    return produced, ordered, (ordered > 0 and produced >= ordered)


def get_effective_order_quantity(order):
    pieces = parse_numeric(order.new_qty_pcs) if order.new_qty_pcs else 0.0
    if not pieces:
        pieces = parse_numeric(order.new_qty_dozen) * 12
    if not pieces:
        pieces = parse_numeric(order.qty)
    return pieces


def get_completed_cut_pieces(order):
    if not get_rates_for_order(order):
        return []
    logs = ProductionLog.query.filter_by(job_no=order.job_no).all()
    completed = []
    for sheet in CuttingSheet.query.filter_by(order_id=order.job_no).order_by(CuttingSheet.id.asc()).all():
        operation_names = list(get_rates_for_cut(order, sheet.cut_no).keys())
        if not operation_names:
            continue
        operation_rates = {
            (rate.operation or '').upper(): rate
            for rate in OperationRate.query.filter(
                func.upper(OperationRate.operation).in_(operation_names)
            ).all()
        }
        stitched_operation_names = {
            operation for operation, rate in operation_rates.items()
            if rate.is_stitched_operation
        }
        cut_logs = [log for log in logs if str(log.cut_no) == str(sheet.cut_no)]
        state = get_cut_production_state(
            order.job_no,
            sheet.cut_no,
            parse_numeric(sheet.quantity),
            operation_names,
            logs=cut_logs,
        )

        cut_complete = True
        for operation_name in operation_names:
            total = state['raw_totals'].get(operation_name, 0)
            limit = state['effective_limits'].get(
                operation_name,
                state['limits_before_bq'].get(operation_name, parse_numeric(sheet.quantity)),
            )
            if operation_name in stitched_operation_names:
                total += state['stitched_bq_totals'].get(operation_name, 0)
                limit = state['limits_before_bq'].get(operation_name, parse_numeric(sheet.quantity))
            if total < limit:
                cut_complete = False
                break

        if not cut_complete:
            continue

        final_operation = operation_names[-1]
        final_logs = [
            log for log in cut_logs
            if (log.operation or '').upper() == final_operation
        ]
        if operation_rates.get(final_operation) and operation_rates[final_operation].is_stitched_operation:
            worker_worked_pcs = sum(log.pcs or 0 for log in final_logs)
            final_pcs_with_bq = worker_worked_pcs + sum(
                parse_numeric(log.bq_stitched) for log in final_logs
            )
        else:
            worker_worked_pcs = 0
            final_pcs_with_bq = state['credited_totals'].get(final_operation, 0)

        if final_pcs_with_bq > 0:
            completed.append({
                'cut_no': sheet.cut_no,
                'pcs': worker_worked_pcs if worker_worked_pcs > 0 else final_pcs_with_bq,
            })
    return completed


def _apportion_whole_quality_pcs(quality_split):
    for item in quality_split:
        total_pcs = max(0, int(item['cut_pcs']))
        exact_aq_pcs = max(0.0, float(item['aq_pcs']))
        whole_aq_pcs = min(total_pcs, math.floor(exact_aq_pcs))
        item['aq_pcs'] = whole_aq_pcs
        item['bq_pcs'] = total_pcs - whole_aq_pcs
        item['_aq_remainder'] = exact_aq_pcs - whole_aq_pcs

    exact_aq_total = sum(item['aq_pcs'] + item['_aq_remainder'] for item in quality_split)
    whole_aq_total = sum(item['aq_pcs'] for item in quality_split)
    round_up_count = max(0, math.floor(exact_aq_total + 0.5 + 1e-10) - whole_aq_total)
    round_up_candidates = sorted(
        (
            item for item in quality_split
            if item['_aq_remainder'] > 0 and item['bq_pcs'] > 0
        ),
        key=lambda item: item['_aq_remainder'],
        reverse=True,
    )
    for item in round_up_candidates[:round_up_count]:
        item['aq_pcs'] += 1
        item['bq_pcs'] -= 1

    for item in quality_split:
        item.pop('_aq_remainder', None)
    return quality_split


def get_cut_quality_split(order):
    if not get_rates_for_order(order):
        return []
    logs = ProductionLog.query.filter_by(job_no=order.job_no).all()
    quality_split = []
    for sheet in CuttingSheet.query.filter_by(order_id=order.job_no).order_by(CuttingSheet.id.asc()).all():
        operation_names = list(get_rates_for_cut(order, sheet.cut_no).keys())
        if not operation_names:
            continue
        operation_rates = {
            (rate.operation or '').upper(): rate
            for rate in OperationRate.query.filter(
                func.upper(OperationRate.operation).in_(operation_names)
            ).all()
        }
        stitched_operation_names = {
            operation for operation, rate in operation_rates.items()
            if rate.is_stitched_operation
        }
        cut_logs = [log for log in logs if str(log.cut_no) == str(sheet.cut_no)]
        if not cut_logs:
            continue
        state = get_cut_production_state(
            order.job_no,
            sheet.cut_no,
            parse_numeric(sheet.quantity),
            operation_names,
            logs=cut_logs,
        )

        cut_complete = True
        for operation_name in operation_names:
            total = state['raw_totals'].get(operation_name, 0)
            limit = state['effective_limits'].get(
                operation_name,
                state['limits_before_bq'].get(operation_name, parse_numeric(sheet.quantity)),
            )
            if operation_name in stitched_operation_names:
                total += state['stitched_bq_totals'].get(operation_name, 0)
                limit = state['limits_before_bq'].get(operation_name, parse_numeric(sheet.quantity))
            if total < limit:
                cut_complete = False
                break
        if not cut_complete:
            continue

        final_operation = operation_names[-1]
        final_logs = [
            log for log in cut_logs
            if (log.operation or '').upper() == final_operation
        ]
        if operation_rates.get(final_operation) and operation_rates[final_operation].is_stitched_operation:
            worker_worked_pcs = sum(log.pcs or 0 for log in final_logs)
            cut_pcs = worker_worked_pcs
        else:
            worker_worked_pcs = state['credited_totals'].get(final_operation, 0)
            cut_pcs = worker_worked_pcs

        worker_worked_pcs = max(0, int(round(worker_worked_pcs)))
        cut_pcs = worker_worked_pcs
        if cut_pcs <= 0:
            continue

        total_fabric_used = 0.0
        fabric_b_used = 0.0
        for inventory in Inventory.query.filter_by(order_id=order.job_no).all():
            cut_usage = 0.0
            for row in inventory.rows:
                if str(row.cut_no) != str(sheet.cut_no):
                    continue
                usage = parse_numeric(row.fabric_use)
                if usage <= 0:
                    continue
                cut_usage += usage
            if cut_usage <= 0:
                continue

            total_fabric_used += cut_usage
            if getattr(inventory, 'fabric_b_enabled', False) and inventory_b_active_for_cut(inventory, int(str(sheet.cut_no)), order.job_no):
                before_cut_state = calculate_inventory_consumption_state(
                    inventory,
                    before_cut_no=int(str(sheet.cut_no)),
                    order_id=order.job_no,
                )
                a_available_before_cut = before_cut_state['a_remaining']
                if a_available_before_cut <= 0:
                    fabric_b_used += cut_usage
                else:
                    fabric_b_used += max(0.0, cut_usage - min(cut_usage, a_available_before_cut))

        fabric_a_ratio = 1.0
        fabric_b_ratio = 0.0
        if total_fabric_used > 0:
            fabric_a_ratio = max(0.0, min(1.0, 1.0 - (fabric_b_used / total_fabric_used)))
            fabric_b_ratio = max(0.0, min(1.0, 1.0 - fabric_a_ratio))

        aq_pcs = max(0.0, worker_worked_pcs * fabric_a_ratio)
        bq_pcs = worker_worked_pcs - aq_pcs
        quality_split.append({
            'cut_no': sheet.cut_no,
            'cut_pcs': cut_pcs,
            'fabric_a_ratio': fabric_a_ratio,
            'fabric_b_ratio': fabric_b_ratio,
            'aq_pcs': aq_pcs,
            'bq_pcs': bq_pcs,
        })
    return _apportion_whole_quality_pcs(quality_split)


def get_order_shipping_snapshot(order):
    quality_split = get_cut_quality_split(order)
    completed_pcs = sum(item['cut_pcs'] for item in quality_split)
    total_aq_pcs = sum(item['aq_pcs'] for item in quality_split)
    total_bq_pcs = sum(item['bq_pcs'] for item in quality_split)

    legacy_shipped_pcs = parse_numeric(order.shipped_pcs)
    shipped_aq_pcs = parse_numeric(getattr(order, 'shipped_aq_pcs', 0))
    shipped_bq_pcs = parse_numeric(getattr(order, 'shipped_bq_pcs', 0))
    if shipped_aq_pcs <= 0 and shipped_bq_pcs <= 0 and legacy_shipped_pcs > 0:
        shipped_aq_pcs = min(legacy_shipped_pcs, total_aq_pcs)
        shipped_bq_pcs = max(0.0, legacy_shipped_pcs - shipped_aq_pcs)

    shipped_pcs = shipped_aq_pcs + shipped_bq_pcs
    balance_aq_pcs = max(0.0, total_aq_pcs - shipped_aq_pcs)
    balance_bq_pcs = max(0.0, total_bq_pcs - shipped_bq_pcs)
    available_pcs = balance_aq_pcs + balance_bq_pcs
    pcs_poly = parse_numeric(order.pcs_poly)
    produced_packets = completed_pcs / pcs_poly if pcs_poly > 0 else 0.0
    available_packets = available_pcs / pcs_poly if pcs_poly > 0 else 0.0
    packets_per_ctn = parse_numeric(order.qty_ctn)
    packets_per_bail = parse_numeric(order.qty_bail)
    return {
        'completed_pcs': completed_pcs,
        'total_order_pcs': parse_numeric(order.new_qty_pcs or order.qty) or parse_numeric(order.new_qty_dozen) * 12,
        'total_aq_pcs': total_aq_pcs,
        'total_bq_pcs': total_bq_pcs,
        'shipped_aq_pcs': shipped_aq_pcs,
        'shipped_bq_pcs': shipped_bq_pcs,
        'shipped_pcs': shipped_pcs,
        'balance_aq_pcs': balance_aq_pcs,
        'balance_bq_pcs': balance_bq_pcs,
        'available_pcs': available_pcs,
        'produced_packets': produced_packets,
        'available_packets': available_packets,
        'packets_per_ctn': packets_per_ctn,
        'packets_per_bail': packets_per_bail,
        'available_ctn': available_packets / packets_per_ctn if packets_per_ctn > 0 else 0.0,
        'available_bails': available_packets / packets_per_bail if packets_per_bail > 0 else 0.0,
    }


def warehouse_finished_goods_by_quality(order_id):
    totals = {'AQ': 0.0, 'BQ': 0.0}
    locations = WarehouseFinishedGoodsLocation.query.filter_by(order_id=order_id).all()
    for location in locations:
        quality = (location.quality or '').upper()
        if quality in totals:
            totals[quality] += max(0.0, parse_numeric(location.quantity))
    return totals


def warehouse_finished_goods_snapshot(order, shipping):
    located = warehouse_finished_goods_by_quality(order.job_no)
    shipping['warehouse_aq_pcs'] = located['AQ']
    shipping['warehouse_bq_pcs'] = located['BQ']
    shipping['dispatchable_aq_pcs'] = min(shipping['balance_aq_pcs'], located['AQ'])
    shipping['dispatchable_bq_pcs'] = min(shipping['balance_bq_pcs'], located['BQ'])
    shipping['dispatchable_pcs'] = (
        shipping['dispatchable_aq_pcs'] + shipping['dispatchable_bq_pcs']
    )
    pcs_per_packet = parse_numeric(order.pcs_poly)
    shipping['dispatchable_packets'] = (
        shipping['dispatchable_pcs'] / pcs_per_packet
        if pcs_per_packet > 0 else 0.0
    )
    shipping['dispatchable_ctn'] = (
        shipping['dispatchable_packets'] / shipping['packets_per_ctn']
        if shipping['packets_per_ctn'] > 0 else 0.0
    )
    shipping['dispatchable_bails'] = (
        shipping['dispatchable_packets'] / shipping['packets_per_bail']
        if shipping['packets_per_bail'] > 0 else 0.0
    )
    return shipping


def consume_warehouse_finished_goods(order_id, quality, quantity, shipment):
    remaining = max(0.0, quantity)
    locations = WarehouseFinishedGoodsLocation.query.filter(
        WarehouseFinishedGoodsLocation.order_id == order_id,
        WarehouseFinishedGoodsLocation.quality == quality,
        WarehouseFinishedGoodsLocation.quantity > 0,
    ).order_by(WarehouseFinishedGoodsLocation.id.asc()).with_for_update().all()
    for location in locations:
        taken = min(location.quantity, remaining)
        if taken <= 0:
            continue
        location.quantity = max(0.0, location.quantity - taken)
        db.session.add(WarehouseFinishedGoodsDispatch(
            shipment=shipment,
            location=location,
            quantity=taken,
        ))
        remaining -= taken
        if remaining <= 0.000001:
            return
    if remaining > 0.000001:
        raise ValueError(f'Not enough warehouse-located {quality} stock for this shipment.')


def stock_portal_access_required():
    return session.get('role') in ('owner', 'manager', 'assistant_manager', 'stock', 'accounts', 'challan')


def get_rejected_recovery_notifications(order_id=None):
    if not order_id:
        return []

    notifications = []
    for inv in Inventory.query.filter_by(order_id=order_id).all():
        if not inv.serial_no:
            continue
        amount = max(0.0, parse_numeric(getattr(inv, 'rejected_recovered_fabric', 0)))
        if amount > 0:
            removed_at = getattr(inv, 'rejected_recovered_removed_at', '') or ''
            notifications.append({
                'serial': inv.serial_no,
                'amount': amount,
                'removed_at': removed_at,
            })
    return notifications

def format_date_ddmmyyyy(value):
    if not value:
        return ''
    text = str(value).strip()
    for fmt in ('%Y-%m-%d', '%d/%m/%Y', '%Y/%m/%d', '%d-%m-%Y'):
        try:
            return datetime.strptime(text, fmt).strftime('%d-%m-%Y')
        except ValueError:
            continue
    return text


def format_date_ddmmyy(value):
    if not value:
        return ''
    text = str(value).strip()
    for fmt in ('%Y-%m-%d', '%d/%m/%Y', '%Y/%m/%d', '%d-%m-%Y'):
        try:
            return datetime.strptime(text, fmt).strftime('%d-%m-%y')
        except ValueError:
            continue
    return text


def normalize_date(value):
    if not value:
        return None
    text = str(value).strip()
    for fmt in ('%Y-%m-%d', '%Y/%m/%d', '%d/%m/%Y', '%d-%m-%Y', '%Y-%m'):
        try:
            return datetime.strptime(text, fmt)
        except ValueError:
            continue
    return None


def ledger_recorded_at(recorded_at, fallback_date):
    if isinstance(recorded_at, datetime):
        return recorded_at
    return normalize_date(recorded_at) or normalize_date(fallback_date) or datetime.min


app.jinja_env.filters['format_ddmmyyyy'] = format_date_ddmmyyyy
app.jinja_env.filters['format_ddmmyy'] = format_date_ddmmyy

def sort_cut_numbers(cuts):
    return sorted(
        cuts,
        key=lambda cut: (0, int(str(cut))) if str(cut).strip().isdigit() else (1, str(cut).casefold())
    )

app.jinja_env.filters['sort_cut_numbers'] = sort_cut_numbers


def update_postgres_schema():
    print("=== update_postgres_schema START ===")

    try:
        inspector = inspect(db.engine)
        print("Tables:", inspector.get_table_names())

        if "production_log" not in inspector.get_table_names():
            print("production_log table not found!")
            return

        existing = [c["name"] for c in inspector.get_columns("production_log")]
        print("Existing columns:", existing)

        required = {
            "file_no": "VARCHAR(50)",
            "party": "VARCHAR(100)",
            "article": "VARCHAR(100)",
            "article_name": "VARCHAR(100)",
            "order_style": "VARCHAR(100)",
            "worker": "VARCHAR(100)",
            "operation": "VARCHAR(100)",
            "pcs": "INTEGER",
            "color": "VARCHAR(50)",
            "cut_no": "VARCHAR(50)",
            "cut_size": "VARCHAR(50)",
            "cut_pcs": "INTEGER",
            "bq_unstitch": "INTEGER",
            "bq_stitched": "INTEGER"
        }

        for col, typ in required.items():
            if col not in existing:
                print(f"Adding {col}...")
                try:
                    db.session.execute(
                        text(
                            f"ALTER TABLE production_log "
                            f"ADD COLUMN IF NOT EXISTS {col} {typ}"
                        )
                    )
                except Exception:
                    db.session.execute(
                        text(
                            f"ALTER TABLE production_log "
                            f"ADD COLUMN {col} {typ}"
                        )
                    )

        db.session.commit()
        print("Schema update complete.")

    except Exception as e:
        db.session.rollback()
        print("SCHEMA UPDATE FAILED")
        traceback.print_exc()


def update_inventory_schema():
    print("=== update_inventory_schema START ===")
    try:
        inspector = inspect(db.engine)
        if "inventory" not in inspector.get_table_names():
            print("inventory table not found!")
            return

        existing = [c["name"] for c in inspector.get_columns("inventory")]
        required = {
            "serial_no": "VARCHAR(100)",
            "order_id": "VARCHAR(100)",
            "recv_date": "VARCHAR(50)",
            "received_from": "VARCHAR(100)",
            "suppliers": "VARCHAR(100)",
            "challan_no": "VARCHAR(100)",
            "place": "VARCHAR(100)",
            "meter_note": "VARCHAR(100)",
            "ms": "VARCHAR(100)",
            "file_no": "VARCHAR(100)",
            "fabric_name": "VARCHAR(100)",
            "fabric_qty_a": "VARCHAR(50)",
            "fabric_qty_b": "VARCHAR(50)",
            "fabric_b_enabled": "BOOLEAN DEFAULT FALSE",
            "fabric_b_activation_cut_no": "INTEGER",
            "fabric_b_activation_order_id": "VARCHAR(100)",
            "fabric_quality": "VARCHAR(100)",
            "cut_size_header": "VARCHAR(100)",
            "width": "VARCHAR(100)",
            "req_cutting": "VARCHAR(100)",
            "receive_cut_pcs": "VARCHAR(50)",
            "fabric_for": "VARCHAR(100)",
            "consumption": "VARCHAR(100)",
            "req_average": "VARCHAR(100)",
            "total": "VARCHAR(100)",
            "used_fabric": "VARCHAR(100)",
            "left_over_fabric": "VARCHAR(100)",
            "rejected_fabric": "VARCHAR(100)",
            "rejected_recovered_fabric": "VARCHAR(100)",
            "rejected_recovered_removed_at": "VARCHAR(50)",
            "a_returned_to_party": "BOOLEAN DEFAULT FALSE",
            "a_returned_quantity": "VARCHAR(50) DEFAULT '0.00'",
            "a_returned_date": "VARCHAR(50) DEFAULT ''",
            "a_returned_by": "VARCHAR(100) DEFAULT ''",
            "a_returned_party": "VARCHAR(200) DEFAULT ''",
            "a_returned_article": "VARCHAR(200) DEFAULT ''",
            "a_returned_shipped": "BOOLEAN DEFAULT FALSE",
            "a_returned_shipped_by": "VARCHAR(100) DEFAULT ''",
            "a_returned_shipped_date": "VARCHAR(50) DEFAULT ''",
            "b_returned_to_party": "BOOLEAN DEFAULT FALSE",
            "b_returned_quantity": "VARCHAR(50) DEFAULT '0.00'",
            "b_returned_date": "VARCHAR(50) DEFAULT ''",
            "b_returned_by": "VARCHAR(100) DEFAULT ''",
            "b_returned_party": "VARCHAR(200) DEFAULT ''",
            "b_returned_article": "VARCHAR(200) DEFAULT ''",
            "b_returned_shipped": "BOOLEAN DEFAULT FALSE",
            "b_returned_shipped_by": "VARCHAR(100) DEFAULT ''",
            "b_returned_shipped_date": "VARCHAR(50) DEFAULT ''"
        }

        for col, typ in required.items():
            if col not in existing:
                print(f"Adding inventory column {col}...")
                db.session.execute(
                    text(
                        f"ALTER TABLE inventory "
                        f"ADD COLUMN {col} {typ}"
                    )
                )

        db.session.commit()
        print("Inventory schema update complete.")

    except Exception as e:
        db.session.rollback()
        print("INVENTORY SCHEMA UPDATE FAILED")
        traceback.print_exc()


def update_shipment_challan_schema():
    try:
        for table_name, columns in {
            'shipment_record': {
                'shipped_by_party': "VARCHAR(30) DEFAULT 'Canon'",
                'shipment_unit_type': "VARCHAR(30) DEFAULT ''",
                'shipped_aq_direct_pcs': 'FLOAT DEFAULT 0.0',
                'shipped_bq_direct_pcs': 'FLOAT DEFAULT 0.0',
                'shipped_aq_packets': 'FLOAT DEFAULT 0.0',
                'shipped_bq_packets': 'FLOAT DEFAULT 0.0',
                'shipped_aq_ctn': 'FLOAT DEFAULT 0.0',
                'shipped_bq_ctn': 'FLOAT DEFAULT 0.0',
                'shipped_aq_bails': 'FLOAT DEFAULT 0.0',
                'shipped_bq_bails': 'FLOAT DEFAULT 0.0',
            },
            'challan_record': {
                'shipped_by_party': "VARCHAR(30) DEFAULT 'Canon'",
                'combined_shipment_ids': "TEXT DEFAULT ''",
                'combined_inventory_ids': "TEXT DEFAULT ''",
                'shipped_aq_pcs': 'FLOAT DEFAULT 0.0',
                'shipped_bq_pcs': 'FLOAT DEFAULT 0.0',
                'shipped_aq_direct_pcs': 'FLOAT DEFAULT 0.0',
                'shipped_bq_direct_pcs': 'FLOAT DEFAULT 0.0',
                'shipped_aq_packets': 'FLOAT DEFAULT 0.0',
                'shipped_bq_packets': 'FLOAT DEFAULT 0.0',
                'shipped_aq_ctn': 'FLOAT DEFAULT 0.0',
                'shipped_bq_ctn': 'FLOAT DEFAULT 0.0',
                'shipped_aq_bails': 'FLOAT DEFAULT 0.0',
                'shipped_bq_bails': 'FLOAT DEFAULT 0.0',
                'shipped_packets': 'FLOAT DEFAULT 0.0',
                'shipped_ctn': 'FLOAT DEFAULT 0.0',
            },
        }.items():
            inspector = inspect(db.engine)
            if table_name not in inspector.get_table_names():
                continue
            existing = {column['name'] for column in inspector.get_columns(table_name)}
            for column_name, column_type in columns.items():
                if column_name not in existing:
                    db.session.execute(text(f'ALTER TABLE {table_name} ADD COLUMN {column_name} {column_type}'))
        db.session.commit()
    except Exception:
        db.session.rollback()
        traceback.print_exc()


def update_order_schema():
    print("=== update_order_schema START ===")
    try:
        inspector = inspect(db.engine)
        if "order" not in inspector.get_table_names():
            print("order table not found!")
            return

        existing = [c["name"] for c in inspector.get_columns("order")]
        required = {
            "article_name": "VARCHAR(100)",
            "year": "VARCHAR(20)",
            "body_size": "VARCHAR(100)",
            "cut_size": "VARCHAR(100)",
            "sample": "VARCHAR(50)",
            "fab_width": "VARCHAR(100)",
            "fab": "VARCHAR(100)",
            "usage": "VARCHAR(100)",
            "margin": "VARCHAR(50)",
            "label": "VARCHAR(100)",
            "label_1": "VARCHAR(100)",
            "label_2": "VARCHAR(100)",
            "label_3": "VARCHAR(100)",
            "rn": "VARCHAR(100)",
            "wash": "VARCHAR(100)",
            "logo": "VARCHAR(50)",
            "emb": "VARCHAR(100)",
            "print": "VARCHAR(100)",
            "poly_size": "VARCHAR(100)",
            "pcs_poly": "VARCHAR(50)",
            "pkt_ctn": "VARCHAR(50)",
            "ctn_size": "VARCHAR(100)",
            "ctn_label": "VARCHAR(100)",
            "barcode": "VARCHAR(100)",
            "qty_ctn": "VARCHAR(50)",
            "qty_bail": "VARCHAR(50)",
            "net_w": "VARCHAR(100)",
            "net_w_bail": "VARCHAR(100)",
            "gross_w": "VARCHAR(100)",
            "gross_w_bail": "VARCHAR(100)",
            "total_ctn": "VARCHAR(50)",
            "total_bails": "VARCHAR(50)",
            "ship_date": "VARCHAR(50)",
            "challan": "VARCHAR(100)",
            "new_qty_dozen": "VARCHAR(50)",
            "new_qty_pcs": "VARCHAR(50)",
            "extension_order_pcs": "VARCHAR(50)",
            "pcs_per_side": "VARCHAR(50)",
            "margin": "VARCHAR(50)",
            "image_file": "VARCHAR(255)",
            "image_files": "TEXT",
            "fulfillment_status": "VARCHAR(30)",
            "shipped_at": "VARCHAR(50)",
            "shipped_by": "VARCHAR(100)",
            "shipped_pcs": "VARCHAR(50) DEFAULT '0'",
            "shipped_aq_pcs": "VARCHAR(50) DEFAULT '0'",
            "shipped_bq_pcs": "VARCHAR(50) DEFAULT '0'",
            "shipped_packets": "VARCHAR(50) DEFAULT '0'",
            "shipped_ctn": "VARCHAR(50) DEFAULT '0'",
            "shipped_bails": "VARCHAR(50) DEFAULT '0'",
            "delivered_at": "VARCHAR(50)",
            "delivered_by": "VARCHAR(100)"
        }

        for col, typ in required.items():
            if col not in existing:
                print(f"Adding order column {col}...")
                db.session.execute(text(f'ALTER TABLE "order" ADD COLUMN {col} {typ}'))

        db.session.commit()
        print("Order schema update complete.")

    except Exception as e:
        db.session.rollback()
        print("ORDER SCHEMA UPDATE FAILED")
        traceback.print_exc()


def update_article_schema():
    print("=== update_article_schema START ===")
    try:
        inspector = inspect(db.engine)
        if "article" not in inspector.get_table_names():
            print("article table not found!")
            return

        existing = [c["name"] for c in inspector.get_columns("article")]
        required = {
            "pcs_per_side": "VARCHAR(50)",
            "margin": "VARCHAR(50)"
        }

        for col, typ in required.items():
            if col not in existing:
                print(f"Adding article column {col}...")
                db.session.execute(text(f'ALTER TABLE "article" ADD COLUMN {col} {typ}'))

        db.session.commit()
        print("Article schema update complete.")

    except Exception as e:
        db.session.rollback()
        print("ARTICLE SCHEMA UPDATE FAILED")
        traceback.print_exc()


def update_worker_schema():
    print("=== update_worker_schema START ===")
    try:
        inspector = inspect(db.engine)
        if "worker" not in inspector.get_table_names():
            print("worker table not found!")
            return

        existing = [c["name"] for c in inspector.get_columns("worker")]
        required = {
            "phone": "VARCHAR(50)",
            "whatsapp_number": "VARCHAR(50)",
            "emergency_number": "VARCHAR(50)",
            "blood_group": "VARCHAR(20)",
            "picture": "VARCHAR(255)",
            "age": "INTEGER",
            "worker_code": "VARCHAR(50)",
            "cnic": "VARCHAR(50)",
            "role": "VARCHAR(50)",
            "dob": "VARCHAR(50)",
            "gender": "VARCHAR(20)",
            "marital_status": "VARCHAR(50)",
            "nationality": "VARCHAR(100)",
            "address": "VARCHAR(255)",
            "city": "VARCHAR(100)",
            "state": "VARCHAR(100)",
            "zip_code": "VARCHAR(50)",
            "supervisor": "VARCHAR(100)",
            "sub_designation": "VARCHAR(100)",
            "joining_date": "VARCHAR(50)",
            "referred_by": "VARCHAR(100)",
            "hired_by": "VARCHAR(100)",
            "salary": "FLOAT",
            "attendance_allowance": "FLOAT",
            "hod": "VARCHAR(100)",
            "employment_type": "VARCHAR(50)",
            "department": "VARCHAR(100)",
            "status": "VARCHAR(20) NOT NULL DEFAULT 'Active'"
        }

        for col, typ in required.items():
            if col not in existing:
                print(f"Adding worker column {col}...")
                db.session.execute(
                    text(
                        f"ALTER TABLE worker "
                        f"ADD COLUMN {col} {typ}"
                    )
                )

        db.session.commit()
        print("Worker schema update complete.")

    except Exception as e:
        db.session.rollback()
        print("WORKER SCHEMA UPDATE FAILED")
        traceback.print_exc()


def update_payment_schema():
    print("=== update_payment_schema START ===")
    try:
        inspector = inspect(db.engine)

        for table_name, required in {
            "worker_advance": {
                "is_paid": "BOOLEAN DEFAULT 0",
                "paid_period": "VARCHAR(80)",
                "paid_at": "VARCHAR(50)"
            },
            "salary_payment": {
                "department": "VARCHAR(100)",
                "payout_portal": "VARCHAR(50)",
                "company": "VARCHAR(30) DEFAULT 'Canon'",
                "period_type": "VARCHAR(30)",
                "period_label": "VARCHAR(120)",
                "period_start": "VARCHAR(20)",
                "period_end": "VARCHAR(20)",
                "amount": "FLOAT DEFAULT 0",
                "paid_at": "VARCHAR(50)"
            },
            "utility_bill": {
                "company": "VARCHAR(30) DEFAULT 'Canon'",
            },
            "utility_bill_payment": {
                "tid": "VARCHAR(100) DEFAULT ''",
                "proof_of_payment": "VARCHAR(255) DEFAULT ''",
                "cheque_number": "VARCHAR(100) DEFAULT ''",
                "cheque_image": "VARCHAR(255) DEFAULT ''",
            },
            "manual_credit_debit_entry": {
                "party_name": "VARCHAR(200) DEFAULT ''",
                "company": "VARCHAR(30) DEFAULT 'Canon'",
            }
        }.items():
            if table_name not in inspector.get_table_names():
                continue
            existing = {c["name"] for c in inspector.get_columns(table_name)}
            for col, typ in required.items():
                if col not in existing:
                    print(f"Adding {table_name} column {col}...")
                    db.session.execute(text(f"ALTER TABLE {table_name} ADD COLUMN {col} {typ}"))
        db.session.commit()
        print("Payment schema update complete.")

    except Exception:
        db.session.rollback()
        print("PAYMENT SCHEMA UPDATE FAILED")
        traceback.print_exc()


def update_receiving_challan_schema():
    print("=== update_receiving_challan_schema START ===")
    try:
        inspector = inspect(db.engine)
        if "receiving_challan" not in inspector.get_table_names():
            print("receiving_challan table not found!")
            return

        existing = [c["name"] for c in inspector.get_columns("receiving_challan")]
        required = {
            "used_file_no": "VARCHAR(100)",
            "place": "VARCHAR(100)",
            "reciever_name": "VARCHAR(100)",
            "per_dozen_consumption": "VARCHAR(50)",
            "required_ctn_bails": "VARCHAR(50)",
            "received_from": "VARCHAR(100)",
            "suppliers": "VARCHAR(100)",
            "meter_to_cm": "VARCHAR(50)",
            "fabric_qty_a": "VARCHAR(50)",
            "fabric_qty_b": "VARCHAR(50)",
            "received_cut_pcs": "VARCHAR(50)",
            "total": "VARCHAR(50)",
            "rolls": "VARCHAR(50)",
            "vehicle_no": "VARCHAR(100)",
            "delivered_by": "VARCHAR(100)",
            "driver_cell_no": "VARCHAR(50)",
            "image_file": "VARCHAR(255)"
        }

        for col, typ in required.items():
            if col not in existing:
                print(f"Adding receiving_challan column {col}...")
                db.session.execute(text(f'ALTER TABLE receiving_challan ADD COLUMN {col} {typ}'))

        db.session.commit()
        print("Receiving challan schema update complete.")

    except Exception as e:
        db.session.rollback()
        print("RECEIVING CHALLAN SCHEMA UPDATE FAILED")
        traceback.print_exc()

# --- CONFIGURATIONS ---
# Operation rates are persisted in the `operation_rate` table. Use `get_rates_dict()` to retrieve them.


ADMIN_USERS = {
    "owner": {"password": "123", "role": "owner", "name": "Muhammad Iqbal (Owner)"},
    "arsalaniqbal": {"password": "canon-arsalan", "role": "manager", "name": "Arsalan Iqbal (Manager)"},
    "assistant1": {"password": "123", "role": "assistant_manager", "name": "Hashir Kamran (Assistant Manager)"},
}


class PortalAccount(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(100), unique=True, nullable=False)
    password = db.Column(db.String(255), nullable=False)
    role = db.Column(db.String(50), nullable=False)
    name = db.Column(db.String(150), nullable=False)
    portal_access = db.Column(db.Text, nullable=False, default='[]')
    page_access = db.Column(db.Text, nullable=True)


class SavedPartyArticleConsumption(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    party_name = db.Column(db.String(150), nullable=False, index=True)
    article_key = db.Column(db.String(150), nullable=False, index=True)
    article_name = db.Column(db.String(150), default='')
    consumption = db.Column(db.Float, default=0.0, nullable=False)
    updated_at = db.Column(db.DateTime, default=datetime.utcnow)

    __table_args__ = (
        db.UniqueConstraint('party_name', 'article_key', name='uq_party_article_consumption'),
    )


def normalize_party_key(value):
    return (value or '').strip().casefold()


def make_article_key(article_label):
    normalized = re.sub(r'[^a-z0-9]+', '_', (article_label or '').lower()).strip('_')
    return normalized or 'article'


def load_party_article_consumption():
    storage = {}
    for record in SavedPartyArticleConsumption.query.all():
        party_key = normalize_party_key(record.party_name)
        if not party_key:
            continue
        article_key = make_article_key(record.article_key or record.article_name)
        if article_key and record.consumption > 0:
            storage.setdefault(party_key, {})[article_key] = float(record.consumption)
    return storage


def save_party_article_consumption(party_name, article_key, consumption_value):
    normalized_party = normalize_party_key(party_name)
    normalized_article = make_article_key(article_key)
    if not normalized_party or not normalized_article:
        return
    parsed_value = parse_numeric(consumption_value)
    if parsed_value > 0:
        record = SavedPartyArticleConsumption.query.filter_by(
            party_name=normalized_party,
            article_key=normalized_article,
        ).first()
        if record is None:
            record = SavedPartyArticleConsumption(
                party_name=normalized_party,
                article_key=normalized_article,
                article_name=(article_key or '').strip(),
            )
        record.article_name = (article_key or '').strip()
        record.consumption = parsed_value
        record.updated_at = datetime.utcnow()
        db.session.add(record)
    else:
        SavedPartyArticleConsumption.query.filter_by(
            party_name=normalized_party,
            article_key=normalized_article,
        ).delete(synchronize_session=False)
    db.session.commit()


def seed_portal_accounts():
    for username, account in ADMIN_USERS.items():
        existing_account = PortalAccount.query.filter_by(username=username).first()
        if not existing_account:
            access = ['manager', 'accounts', 'stock', 'challan'] if account['role'] == 'manager' else ['assistant_manager', 'stock', 'challan'] if account['role'] == 'assistant_manager' else []
            db.session.add(PortalAccount(username=username, portal_access=json.dumps(access), **account))
        elif existing_account.role == 'manager':
            try:
                access = json.loads(existing_account.portal_access or '[]')
            except (TypeError, ValueError):
                access = []
            if not isinstance(access, list):
                access = []
            if 'costing' in access:
                access.remove('costing')
                existing_account.portal_access = json.dumps(access)
            if 'accounts' not in access:
                access.append('accounts')
                existing_account.portal_access = json.dumps(access)
        elif existing_account.role == 'assistant_manager':
            try:
                access = json.loads(existing_account.portal_access or '[]')
            except (TypeError, ValueError):
                access = []
            if not isinstance(access, list):
                access = []
            for portal in ('assistant_manager', 'stock', 'challan'):
                if portal not in access:
                    access.append(portal)
                    existing_account.portal_access = json.dumps(access)
    db.session.commit()


def ensure_portal_account_access_column(engine):
    inspector = inspect(engine)
    if 'portal_account' not in inspector.get_table_names():
        return
    columns = {column['name'] for column in inspector.get_columns('portal_account')}
    if 'portal_access' not in columns:
        with engine.begin() as connection:
            connection.execute(text('ALTER TABLE portal_account ADD COLUMN portal_access TEXT'))
        with engine.begin() as connection:
            connection.execute(text("UPDATE portal_account SET portal_access = '[\"manager\",\"stock\",\"challan\"]' WHERE role = 'manager' AND (portal_access IS NULL OR TRIM(portal_access) = '')"))
            connection.execute(text("UPDATE portal_account SET portal_access = '[\"assistant_manager\",\"stock\",\"challan\"]' WHERE role = 'assistant_manager' AND (portal_access IS NULL OR TRIM(portal_access) = '')"))
            connection.execute(text("UPDATE portal_account SET portal_access = '[]' WHERE portal_access IS NULL OR TRIM(portal_access) = ''"))


def ensure_portal_account_page_access_column(engine):
    inspector = inspect(engine)
    if 'portal_account' not in inspector.get_table_names():
        return
    columns = {column['name'] for column in inspector.get_columns('portal_account')}
    if 'page_access' not in columns:
        with engine.begin() as connection:
            connection.execute(text('ALTER TABLE portal_account ADD COLUMN page_access TEXT'))


def ensure_item_master_issue_columns(engine):
    inspector = inspect(engine)
    if 'item_master' not in inspector.get_table_names():
        return
    columns = {column['name'] for column in inspector.get_columns('item_master')}
    with engine.begin() as connection:
        if 'issue_unit' not in columns:
            connection.execute(text("ALTER TABLE item_master ADD COLUMN issue_unit VARCHAR(50) DEFAULT ''"))
        if 'issue_unit_factor' not in columns:
            connection.execute(text('ALTER TABLE item_master ADD COLUMN issue_unit_factor FLOAT NOT NULL DEFAULT 1'))


def is_read_only_profile():
    return (
        session.get('role') == 'assistant_manager'
        or session.get('profile_role') == 'operations_manager'
    )


def reject_read_only_edit(message='This profile has read-only access to saved entries.'):
    flash(message, 'danger')
    return redirect(request.referrer or url_for('manager_dashboard'))


def delete_order_and_dependencies(order):
    if order is None:
        return False

    job_no = order.job_no
    order_id = order.id
    if job_no and CuttingTransfer.query.filter(
        or_(
            CuttingTransfer.source_order_id == order_id,
            CuttingTransfer.destination_order_id == order_id,
        )
    ).first():
        return False

    article_record = order.article_ref or Article.query.filter_by(
        article_no=normalize_article_no(order.article)
    ).first()

    if job_no:
        ProductionLog.query.filter_by(job_no=job_no).delete(synchronize_session=False)
        SavedRequirement.query.filter_by(order_id=job_no).delete(synchronize_session=False)
        ReceivingChallan.query.filter_by(order_id=job_no).delete(synchronize_session=False)

        inventory_ids = [item.id for item in Inventory.query.filter_by(order_id=job_no).all()]
        if inventory_ids:
            InventoryRow.query.filter(InventoryRow.inventory_id.in_(inventory_ids)).delete(synchronize_session=False)
            InventorySecondRow.query.filter(InventorySecondRow.inventory_id.in_(inventory_ids)).delete(synchronize_session=False)
        Inventory.query.filter_by(order_id=job_no).delete(synchronize_session=False)

        cutting_sheet_ids = [sheet.id for sheet in CuttingSheet.query.filter_by(order_id=job_no).all()]
        if cutting_sheet_ids:
            CuttingSheetRow.query.filter(CuttingSheetRow.cutting_sheet_id.in_(cutting_sheet_ids)).delete(synchronize_session=False)
        CuttingSheet.query.filter_by(order_id=job_no).delete(synchronize_session=False)

    OrderOperationRate.query.filter_by(order_id=order_id).delete(synchronize_session=False)
    OperationRateHistory.query.filter_by(order_id=order_id).delete(synchronize_session=False)

    db.session.delete(order)

    db.session.commit()
    return True

WORKERS_DB = {
    "AHMED": "ahmed@canon.com", 
    "SULTAN": "sultan@canon.com", 
    "IKRAM": "ikram@canon.com", 
    "NASIR": "nasir@canon.com", 
    "YOUNUS": "younus@canon.com"
}


# --- DATABASE MODEL ---
class Article(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    article_no = db.Column(db.String(50), unique=True, nullable=False)
    article_name = db.Column(db.String(100))
    party_name = db.Column(db.String(100))
    color = db.Column(db.String(50))
    style = db.Column(db.String(50))
    finish_size = db.Column(db.String(50), default='')
    length = db.Column(db.String(50), default='')
    width = db.Column(db.String(50), default='')
    fabric_type = db.Column(db.String(100), default='')
    pcs_per_side = db.Column(db.String(50))
    margin = db.Column(db.String(50))
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    orders = db.relationship('Order', backref='article_ref', lazy=True, cascade='all, delete-orphan')
    material_specs = db.relationship('ArticleMaterialSpec', backref='article', cascade='all, delete-orphan', lazy=True)


class ArticleMaterialSpec(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    article_id = db.Column(db.Integer, db.ForeignKey('article.id'), nullable=False, index=True)
    item_name = db.Column(db.String(150), nullable=False)
    material = db.Column(db.String(150), default='')
    size = db.Column(db.String(50), default='')
    qty_per_piece = db.Column(db.String(50), default='')
    unit = db.Column(db.String(50), default='')
    item_type = db.Column(db.String(50), default='')
    sort_order = db.Column(db.Integer, default=0, nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)


class Vendor(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(150), unique=True, nullable=False)
    code = db.Column(db.String(50), unique=True, nullable=True)
    contact_person = db.Column(db.String(150), default='')
    phone = db.Column(db.String(50), default='')
    email = db.Column(db.String(150), default='')
    address = db.Column(db.String(255), default='')
    notes = db.Column(db.Text, default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    items = db.relationship('VendorItem', backref='vendor', cascade='all, delete-orphan', lazy=True)


class ItemMaster(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    item_name = db.Column(db.String(150), unique=True, nullable=False)
    material = db.Column(db.String(150), default='')
    size = db.Column(db.String(50), default='')
    unit = db.Column(db.String(50), default='')
    issue_unit = db.Column(db.String(50), default='')
    issue_unit_factor = db.Column(db.Float, nullable=False, default=1.0)
    returnable = db.Column(db.Boolean, nullable=False, default=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)


class VendorItem(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    vendor_id = db.Column(db.Integer, db.ForeignKey('vendor.id'), nullable=False, index=True)
    item_name = db.Column(db.String(150), nullable=False)
    material = db.Column(db.String(150), default='')
    size = db.Column(db.String(50), default='')
    unit = db.Column(db.String(50), default='pcs')
    pack_qty = db.Column(db.Float, default=0.0)
    pack_price = db.Column(db.Float, default=0.0)
    rate = db.Column(db.Float, default=0.0)
    notes = db.Column(db.Text, default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow)


class Order(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    job_no = db.Column(db.String(50))
    date = db.Column(db.String(20))
    name = db.Column(db.String(100))
    file_no = db.Column(db.String(50))
    cut_no = db.Column(db.String(50))
    article = db.Column(db.String(100))
    article_name = db.Column(db.String(100))
    article_id = db.Column(db.Integer, db.ForeignKey('article.id'))
    po_no = db.Column(db.String(50))
    style = db.Column(db.String(50))
    color = db.Column(db.String(50))
    qty = db.Column(db.String(50))
    new_qty_dozen = db.Column(db.String(50))
    new_qty_pcs = db.Column(db.String(50))
    extension_order_pcs = db.Column(db.String(50), default='0')
    year = db.Column(db.String(20))
    body_size = db.Column(db.String(100))
    cut_size = db.Column(db.String(100))
    sample = db.Column(db.String(50))
    fab_width = db.Column(db.String(100))
    fab = db.Column(db.String(100))
    usage = db.Column(db.String(100))
    margin = db.Column(db.String(50))
    pcs_per_side = db.Column(db.String(50))
    label = db.Column(db.String(100))
    label_1 = db.Column(db.String(100))
    label_2 = db.Column(db.String(100))
    label_3 = db.Column(db.String(100))
    rn = db.Column(db.String(100))
    wash = db.Column(db.String(100))
    logo = db.Column(db.String(50))
    emb = db.Column(db.String(100))
    print_field = db.Column('print', db.String(100))
    poly_size = db.Column(db.String(100))
    pcs_poly = db.Column(db.String(50))
    pkt_ctn = db.Column(db.String(50))
    ctn_size = db.Column(db.String(100))
    ctn_label = db.Column(db.String(100))
    barcode = db.Column(db.String(100))
    qty_ctn = db.Column(db.String(50))
    qty_bail = db.Column(db.String(50))
    net_w = db.Column(db.String(100))
    net_w_bail = db.Column(db.String(100))
    gross_w = db.Column(db.String(100))
    gross_w_bail = db.Column(db.String(100))
    total_ctn = db.Column(db.String(50))
    total_bails = db.Column(db.String(50))
    ship_date = db.Column(db.String(50))
    challan = db.Column(db.String(100))
    image_file = db.Column(db.String(255))
    image_files = db.Column(db.Text, default='[]')
    fulfillment_status = db.Column(db.String(30), default='PENDING')
    shipped_at = db.Column(db.String(50))
    shipped_by = db.Column(db.String(100))
    shipped_pcs = db.Column(db.String(50), default='0')
    shipped_aq_pcs = db.Column(db.String(50), default='0')
    shipped_bq_pcs = db.Column(db.String(50), default='0')
    shipped_packets = db.Column(db.String(50), default='0')
    shipped_ctn = db.Column(db.String(50), default='0')
    shipped_bails = db.Column(db.String(50), default='0')
    delivered_at = db.Column(db.String(50))
    delivered_by = db.Column(db.String(100))
    shipments = db.relationship('ShipmentRecord', back_populates='order', cascade='all, delete-orphan')


class ShipmentRecord(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    order_id = db.Column(db.Integer, db.ForeignKey('order.id'), nullable=False, index=True)
    job_no = db.Column(db.String(50), nullable=False, index=True)
    shipped_at = db.Column(db.String(50), default='')
    shipped_by = db.Column(db.String(100), default='')
    shipped_aq_pcs = db.Column(db.Float, default=0.0)
    shipped_bq_pcs = db.Column(db.Float, default=0.0)
    shipped_aq_direct_pcs = db.Column(db.Float, default=0.0)
    shipped_bq_direct_pcs = db.Column(db.Float, default=0.0)
    shipped_aq_packets = db.Column(db.Float, default=0.0)
    shipped_bq_packets = db.Column(db.Float, default=0.0)
    shipped_aq_ctn = db.Column(db.Float, default=0.0)
    shipped_bq_ctn = db.Column(db.Float, default=0.0)
    shipped_aq_bails = db.Column(db.Float, default=0.0)
    shipped_bq_bails = db.Column(db.Float, default=0.0)
    shipped_pcs = db.Column(db.Float, default=0.0)
    shipped_packets = db.Column(db.Float, default=0.0)
    shipped_ctn = db.Column(db.Float, default=0.0)
    shipped_bails = db.Column(db.Float, default=0.0)
    shipment_unit_type = db.Column(db.String(30), default='')
    ctn_percent = db.Column(db.Float, default=0.0)
    bail_percent = db.Column(db.Float, default=0.0)
    shipped_by_party = db.Column(db.String(30), default='Canon')
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    order = db.relationship('Order', back_populates='shipments')
    warehouse_dispatches = db.relationship(
        'WarehouseFinishedGoodsDispatch',
        back_populates='shipment',
        cascade='all, delete-orphan',
        lazy=True,
    )


class WarehouseFinishedGoodsLocation(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    order_id = db.Column(db.String(50), nullable=False, index=True)
    quality = db.Column(db.String(2), nullable=False, index=True)
    location_type = db.Column(db.String(20), nullable=False)
    department = db.Column(db.String(100), nullable=False)
    room = db.Column(db.String(100), nullable=False)
    gala = db.Column(db.String(100), default='')
    rack_no = db.Column(db.String(50), default='')
    shelf_no = db.Column(db.String(50), default='')
    quantity = db.Column(db.Float, nullable=False, default=0.0)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    dispatches = db.relationship(
        'WarehouseFinishedGoodsDispatch',
        back_populates='location',
        lazy=True,
    )


class WarehouseFinishedGoodsDispatch(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    shipment_id = db.Column(
        db.Integer,
        db.ForeignKey('shipment_record.id', ondelete='CASCADE'),
        nullable=False,
        index=True,
    )
    location_id = db.Column(
        db.Integer,
        db.ForeignKey('warehouse_finished_goods_location.id'),
        nullable=False,
        index=True,
    )
    quantity = db.Column(db.Float, nullable=False)
    shipment = db.relationship('ShipmentRecord', back_populates='warehouse_dispatches')
    location = db.relationship('WarehouseFinishedGoodsLocation', back_populates='dispatches')


class ChallanRecord(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    challan_no = db.Column(db.String(50), unique=True, nullable=False, index=True)
    source_type = db.Column(db.String(30), nullable=False, default='order')
    shipment_id = db.Column(db.Integer, nullable=True, index=True)
    combined_shipment_ids = db.Column(db.Text, default='')
    combined_inventory_ids = db.Column(db.Text, default='')
    inventory_id = db.Column(db.Integer, nullable=True, index=True)
    order_id = db.Column(db.Integer, nullable=True, index=True)
    job_no = db.Column(db.String(100), default='')
    party_name = db.Column(db.String(200), default='')
    article_name = db.Column(db.String(200), default='')
    challan_date = db.Column(db.String(50), default='')
    shipped_pcs = db.Column(db.Float, default=0.0)
    shipped_meter = db.Column(db.Float, default=0.0)
    shipped_aq_pcs = db.Column(db.Float, default=0.0)
    shipped_bq_pcs = db.Column(db.Float, default=0.0)
    shipped_aq_direct_pcs = db.Column(db.Float, default=0.0)
    shipped_bq_direct_pcs = db.Column(db.Float, default=0.0)
    shipped_aq_packets = db.Column(db.Float, default=0.0)
    shipped_bq_packets = db.Column(db.Float, default=0.0)
    shipped_aq_ctn = db.Column(db.Float, default=0.0)
    shipped_bq_ctn = db.Column(db.Float, default=0.0)
    shipped_aq_bails = db.Column(db.Float, default=0.0)
    shipped_bq_bails = db.Column(db.Float, default=0.0)
    shipped_packets = db.Column(db.Float, default=0.0)
    shipped_ctn = db.Column(db.Float, default=0.0)
    shipped_bails = db.Column(db.Float, default=0.0)
    shipped_by_party = db.Column(db.String(30), default='Canon')
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow)


class BillingInvoice(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    invoice_no = db.Column(db.String(50), unique=True, nullable=False, index=True)
    challan_id = db.Column(db.Integer, db.ForeignKey('challan_record.id', ondelete='RESTRICT'), unique=True, nullable=False, index=True)
    party_name = db.Column(db.String(200), nullable=False, default='')
    party_address = db.Column(db.String(255), default='')
    party_city = db.Column(db.String(100), default='')
    party_ntn = db.Column(db.String(50), default='')
    sales_tax_no = db.Column(db.String(50), default='')
    invoice_date = db.Column(db.String(10), nullable=False)
    due_date = db.Column(db.String(10), default='')
    currency = db.Column(db.String(10), nullable=False, default='PKR')
    subtotal = db.Column(db.Float, nullable=False, default=0.0)
    legacy_discount = db.Column('discount', db.Float, nullable=False, default=0.0)
    tax_rate = db.Column(db.Float, nullable=False, default=0.0)
    tax_amount = db.Column(db.Float, nullable=False, default=0.0)
    further_tax_rate = db.Column(db.Float, nullable=False, default=0.0)
    further_tax_amount = db.Column(db.Float, nullable=False, default=0.0)
    total = db.Column(db.Float, nullable=False, default=0.0)
    notes = db.Column(db.Text, default='')
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    challan = db.relationship('ChallanRecord', backref=db.backref('billing_invoice', uselist=False))
    lines = db.relationship('BillingInvoiceLine', backref='invoice', cascade='all, delete-orphan', lazy=True)
    payments = db.relationship('BillingPayment', backref='invoice', cascade='all, delete-orphan', lazy=True)
    challan_links = db.relationship('BillingInvoiceChallan', back_populates='invoice', cascade='all, delete-orphan', lazy=True)

    @property
    def billing_challans(self):
        challans = {link.challan.id: link.challan for link in self.challan_links}
        if self.challan:
            challans.setdefault(self.challan.id, self.challan)
        return sorted(challans.values(), key=lambda challan: challan.id)


class BillingInvoiceChallan(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    invoice_id = db.Column(db.Integer, db.ForeignKey('billing_invoice.id', ondelete='CASCADE'), nullable=False, index=True)
    challan_id = db.Column(db.Integer, db.ForeignKey('challan_record.id', ondelete='RESTRICT'), nullable=False, index=True)
    __table_args__ = (db.UniqueConstraint('invoice_id', 'challan_id', name='uq_billing_invoice_challan'),)
    invoice = db.relationship('BillingInvoice', back_populates='challan_links')
    challan = db.relationship('ChallanRecord')


class BillingParty(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    shipper = db.Column(db.String(30), nullable=False, index=True)
    party_name = db.Column(db.String(200), nullable=False)
    contact_person = db.Column(db.String(150), default='')
    phone = db.Column(db.String(50), default='')
    email = db.Column(db.String(150), default='')
    address = db.Column(db.String(255), default='')
    city = db.Column(db.String(100), default='')
    ntn = db.Column(db.String(50), default='')
    sales_tax_no = db.Column(db.String(50), default='')
    notes = db.Column(db.String(500), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    __table_args__ = (db.UniqueConstraint('shipper', 'party_name', name='uq_billing_party_shipper_name'),)


class BillingInvoiceLine(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    invoice_id = db.Column(db.Integer, db.ForeignKey('billing_invoice.id', ondelete='CASCADE'), nullable=False, index=True)
    challan_id = db.Column(db.Integer, db.ForeignKey('challan_record.id', ondelete='RESTRICT'), nullable=True, index=True)
    shipment_id = db.Column(db.Integer, db.ForeignKey('shipment_record.id'), nullable=True, index=True)
    job_no = db.Column(db.String(100), nullable=False, default='')
    article = db.Column(db.String(200), nullable=False, default='')
    description = db.Column(db.String(300), nullable=False, default='')
    quantity = db.Column(db.Float, nullable=False, default=0.0)
    unit = db.Column(db.String(20), nullable=False, default='PCS')
    unit_rate = db.Column(db.Float, nullable=False, default=0.0)
    amount = db.Column(db.Float, nullable=False, default=0.0)
    challan = db.relationship('ChallanRecord')


class BillingPayment(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    invoice_id = db.Column(db.Integer, db.ForeignKey('billing_invoice.id', ondelete='CASCADE'), nullable=False, index=True)
    amount = db.Column(db.Float, nullable=False)
    paid_on = db.Column(db.String(10), nullable=False)
    method = db.Column(db.String(30), nullable=False, default='Cash')
    reference = db.Column(db.String(100), default='')
    notes = db.Column(db.String(500), default='')
    received_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class BillingNotification(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    shipper = db.Column(db.String(30), nullable=False, index=True)
    notification_type = db.Column(db.String(40), nullable=False)
    reference_key = db.Column(db.String(100), nullable=False)
    title = db.Column(db.String(200), nullable=False)
    message = db.Column(db.String(500), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)
    resolved_at = db.Column(db.DateTime, nullable=True, index=True)


class CustomerBill(db.Model):
    __tablename__ = 'customer_bill'

    id = db.Column(db.Integer, primary_key=True)
    bill_no = db.Column(db.String(50), nullable=False, unique=True, index=True)
    challan_id = db.Column(db.Integer, db.ForeignKey('challan_record.id', ondelete='RESTRICT'), nullable=False, index=True)
    party_name = db.Column(db.String(200), nullable=False, default='')
    customer_address = db.Column(db.String(255), nullable=False, default='')
    customer_phone = db.Column(db.String(50), nullable=False, default='')
    invoice_date = db.Column(db.String(10), nullable=False)
    due_date = db.Column(db.String(10), default='')
    currency = db.Column(db.String(10), nullable=False, default='PKR')
    subtotal = db.Column(db.Float, nullable=False, default=0.0)
    legacy_discount = db.Column('discount', db.Float, nullable=False, default=0.0)
    tax_rate = db.Column(db.Float, nullable=False, default=0.0)
    tax_amount = db.Column(db.Float, nullable=False, default=0.0)
    further_tax_rate = db.Column(db.Float, nullable=False, default=0.0)
    further_tax_amount = db.Column(db.Float, nullable=False, default=0.0)
    total = db.Column(db.Float, nullable=False, default=0.0)
    notes = db.Column(db.Text, default='')
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    challan = db.relationship('ChallanRecord', backref=db.backref('customer_bill', uselist=False))
    lines = db.relationship('CustomerBillLine', backref='bill', cascade='all, delete-orphan', lazy=True)
    payments = db.relationship('CustomerBillPayment', backref='bill', cascade='all, delete-orphan', lazy=True)
    challan_links = db.relationship('CustomerBillChallan', back_populates='bill', cascade='all, delete-orphan', lazy=True)

    @property
    def billing_challans(self):
        challans = {link.challan.id: link.challan for link in self.challan_links}
        if self.challan:
            challans.setdefault(self.challan.id, self.challan)
        return sorted(challans.values(), key=lambda challan: challan.id)


class CustomerBillChallan(db.Model):
    __tablename__ = 'customer_bill_challan'

    id = db.Column(db.Integer, primary_key=True)
    bill_id = db.Column(db.Integer, db.ForeignKey('customer_bill.id', ondelete='CASCADE'), nullable=False, index=True)
    challan_id = db.Column(db.Integer, db.ForeignKey('challan_record.id', ondelete='RESTRICT'), nullable=False, index=True)
    __table_args__ = (db.UniqueConstraint('bill_id', 'challan_id', name='uq_customer_bill_challan'),)
    bill = db.relationship('CustomerBill', back_populates='challan_links')
    challan = db.relationship('ChallanRecord')


class CustomerBillLine(db.Model):
    __tablename__ = 'customer_bill_line'

    id = db.Column(db.Integer, primary_key=True)
    bill_id = db.Column(db.Integer, db.ForeignKey('customer_bill.id', ondelete='CASCADE'), nullable=False, index=True)
    challan_id = db.Column(db.Integer, db.ForeignKey('challan_record.id', ondelete='RESTRICT'), nullable=True, index=True)
    shipment_id = db.Column(db.Integer, db.ForeignKey('shipment_record.id'), nullable=True, index=True)
    job_no = db.Column(db.String(100), nullable=False, default='')
    article = db.Column(db.String(200), nullable=False, default='')
    description = db.Column(db.String(300), nullable=False, default='')
    quantity = db.Column(db.Float, nullable=False, default=0.0)
    unit = db.Column(db.String(20), nullable=False, default='PCS')
    unit_rate = db.Column(db.Float, nullable=False, default=0.0)
    amount = db.Column(db.Float, nullable=False, default=0.0)
    challan = db.relationship('ChallanRecord')


class CustomerBillArticleNote(db.Model):
    __tablename__ = 'customer_bill_article_note'

    id = db.Column(db.Integer, primary_key=True)
    bill_id = db.Column(db.Integer, db.ForeignKey('customer_bill.id', ondelete='CASCADE'), nullable=False, index=True)
    article_key = db.Column(db.String(300), nullable=False)
    note = db.Column(db.Text, nullable=False, default='')
    updated_at = db.Column(db.DateTime, nullable=False, default=datetime.utcnow, onupdate=datetime.utcnow)
    __table_args__ = (db.UniqueConstraint('bill_id', 'article_key', name='uq_customer_bill_article_note'),)


class CustomerBillPayment(db.Model):
    __tablename__ = 'customer_bill_payment'

    id = db.Column(db.Integer, primary_key=True)
    bill_id = db.Column(db.Integer, db.ForeignKey('customer_bill.id', ondelete='CASCADE'), nullable=False, index=True)
    amount = db.Column(db.Float, nullable=False)
    paid_on = db.Column(db.String(10), nullable=False)
    method = db.Column(db.String(30), nullable=False, default='Cash')
    reference = db.Column(db.String(100), default='')
    notes = db.Column(db.String(500), default='')
    received_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class UtilityBill(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    utility_type = db.Column(db.String(30), nullable=False, index=True)
    provider = db.Column(db.String(150), nullable=False)
    account_reference = db.Column(db.String(100), default='')
    billing_period = db.Column(db.String(20), nullable=False, index=True)
    bill_date = db.Column(db.String(10), nullable=False)
    due_date = db.Column(db.String(10), default='')
    amount = db.Column(db.Float, nullable=False)
    company = db.Column(db.String(30), nullable=False, default='Canon')
    notes = db.Column(db.String(500), default='')
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    payments = db.relationship('UtilityBillPayment', backref='bill', cascade='all, delete-orphan', lazy=True)


class UtilityBillPayment(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    bill_id = db.Column(db.Integer, db.ForeignKey('utility_bill.id', ondelete='CASCADE'), nullable=False, index=True)
    amount = db.Column(db.Float, nullable=False)
    paid_on = db.Column(db.String(10), nullable=False)
    method = db.Column(db.String(30), nullable=False, default='Bank Transfer')
    reference = db.Column(db.String(100), default='')
    tid = db.Column(db.String(100), nullable=False, default='')
    proof_of_payment = db.Column(db.String(255), nullable=False, default='')
    cheque_number = db.Column(db.String(100), nullable=False, default='')
    cheque_image = db.Column(db.String(255), nullable=False, default='')
    notes = db.Column(db.String(500), default='')
    paid_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class UtilityBillSummary(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    utility_bill_id = db.Column(db.Integer, db.ForeignKey('utility_bill.id', ondelete='CASCADE'), nullable=False, index=True)
    title = db.Column(db.String(200), nullable=False, default='')
    invoice_to = db.Column(db.String(200), nullable=False, default='')
    bank_name = db.Column(db.String(100), nullable=False, default='')
    invoice_no = db.Column(db.String(40), unique=True, nullable=True, index=True)
    invoice_date = db.Column(db.String(10), nullable=False, default='')
    cheque_image = db.Column(db.String(255), nullable=False, default='')
    rows_json = db.Column(db.Text, nullable=False, default='[]')
    total_amount = db.Column(db.Float, nullable=False, default=0.0)
    notes = db.Column(db.String(500), default='')
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    utility_bill = db.relationship('UtilityBill', backref=db.backref('summaries', cascade='all, delete-orphan', lazy=True))


class ManualCreditDebitEntry(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    date = db.Column(db.String(10), nullable=False, index=True)
    direction = db.Column(db.String(6), nullable=False, index=True)
    description = db.Column(db.String(255), nullable=False)
    reference = db.Column(db.String(100), default='')
    method = db.Column(db.String(50), default='Manual')
    amount = db.Column(db.Float, nullable=False)
    party_name = db.Column(db.String(200), default='')
    company = db.Column(db.String(30), nullable=False, default='Canon')
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class PettyCashEntry(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    date = db.Column(db.String(10), nullable=False, index=True)
    month_key = db.Column(db.String(7), nullable=False, index=True)
    transaction_type = db.Column(db.String(20), nullable=False, index=True)
    company = db.Column(db.String(30), nullable=False, index=True)
    description = db.Column(db.String(255), nullable=False)
    amount = db.Column(db.Float, nullable=False)
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class PettyCashMonthClose(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    month_key = db.Column(db.String(7), nullable=False)
    company = db.Column(db.String(30), nullable=False)
    returned_amount = db.Column(db.Float, nullable=False, default=0)
    company_ledger_entry_id = db.Column(
        db.Integer, db.ForeignKey('manual_credit_debit_entry.id')
    )
    closed_at = db.Column(db.DateTime, nullable=False, default=datetime.utcnow)
    __table_args__ = (
        db.UniqueConstraint('month_key', 'company', name='uq_petty_cash_month_company'),
    )


def normalize_challan_shipper(value):
    shipper = (value or 'Canon').strip().title()
    return shipper if shipper in ('Canon', 'Haram') else 'Canon'


def format_challan_number(value):
    text = str(value or '').upper().strip()
    if not text:
        return ''

    match = re.search(r'(?:(?:CANON|HARAM)[- ]?)?CH-(\d+)', text)
    if match:
        prefix = 'C' if 'CANON' in text or text.startswith('C') else 'H'
        return f"{prefix}-{int(match.group(1)):04d}"

    match = re.search(r'([CH])-(\d+)', text)
    if match:
        return f"{match.group(1)}-{int(match.group(2)):04d}"

    match = re.search(r'\b(\d+)\b', text)
    if match and text.startswith(('C', 'H')):
        return f"{text[0]}-{int(match.group(1)):04d}"

    return text


app.jinja_env.globals['format_challan_number'] = format_challan_number


def next_challan_number(shipper='Canon'):
    shipper = normalize_challan_shipper(shipper)
    prefix = 'C' if shipper == 'Canon' else 'H'
    serials = []
    for challan in ChallanRecord.query.all():
        normalized = format_challan_number(challan.challan_no)
        if normalized.startswith(f'{prefix}-'):
            try:
                serials.append(int(normalized.split('-')[-1]))
            except (TypeError, ValueError):
                pass
    next_serial = max(serials, default=0) + 1
    return f"{prefix}-{next_serial:04d}"


def normalize_challan_number_sequences():
    counters = {'Canon': 0, 'Haram': 0}
    challans = ChallanRecord.query.order_by(ChallanRecord.id.asc()).all()

    # Move every record to a temporary unique value before assigning the
    # independent Canon and Haram sequences required by the unique column.
    for challan in challans:
        challan.challan_no = f'RENUMBER-{challan.id}'
    db.session.flush()

    for challan in challans:
        shipper = normalize_challan_shipper(challan.shipped_by_party)
        counters[shipper] += 1
        prefix = 'C' if shipper == 'Canon' else 'H'
        challan.challan_no = f'{prefix}-{counters[shipper]:04d}'


def ensure_shipment_challans():
    # A returned-fabric inventory item can belong to only one combined challan.
    # Keep it on the newest challan and remove stale duplicate references.
    claimed_inventory_ids = set()
    grouped_challans = ChallanRecord.query.filter(
        ChallanRecord.source_type == 'order',
        ChallanRecord.combined_inventory_ids.isnot(None),
    ).order_by(ChallanRecord.id.desc()).all()
    for grouped_challan in grouped_challans:
        try:
            inventory_ids = json.loads(grouped_challan.combined_inventory_ids or '[]')
        except (TypeError, ValueError):
            inventory_ids = []
        unique_inventory_ids = [
            inventory_id for inventory_id in inventory_ids
            if inventory_id not in claimed_inventory_ids
        ]
        claimed_inventory_ids.update(unique_inventory_ids)
        if unique_inventory_ids != inventory_ids:
            grouped_challan.combined_inventory_ids = json.dumps(unique_inventory_ids)

    for shipment in ShipmentRecord.query.order_by(ShipmentRecord.id.asc()).all():
        challan = ChallanRecord.query.filter_by(shipment_id=shipment.id, source_type='order').first()
        if not challan:
            for grouped_challan in ChallanRecord.query.filter_by(source_type='order').all():
                try:
                    grouped_shipment_ids = json.loads(grouped_challan.combined_shipment_ids or '[]')
                except (TypeError, ValueError):
                    grouped_shipment_ids = []
                if shipment.id in grouped_shipment_ids:
                    challan = grouped_challan
                    break
        if challan:
            try:
                if len(json.loads(challan.combined_shipment_ids or '[]')) > 1:
                    continue
            except (TypeError, ValueError):
                pass
            if challan.shipment_id != shipment.id:
                continue
            challan.shipped_pcs = parse_numeric(shipment.shipped_pcs)
            challan.shipped_aq_pcs = parse_numeric(getattr(shipment, 'shipped_aq_pcs', 0))
            challan.shipped_bq_pcs = parse_numeric(getattr(shipment, 'shipped_bq_pcs', 0))
            challan.shipped_aq_direct_pcs = parse_numeric(getattr(shipment, 'shipped_aq_direct_pcs', 0))
            challan.shipped_bq_direct_pcs = parse_numeric(getattr(shipment, 'shipped_bq_direct_pcs', 0))
            challan.shipped_aq_packets = parse_numeric(getattr(shipment, 'shipped_aq_packets', 0))
            challan.shipped_bq_packets = parse_numeric(getattr(shipment, 'shipped_bq_packets', 0))
            challan.shipped_aq_ctn = parse_numeric(getattr(shipment, 'shipped_aq_ctn', 0))
            challan.shipped_bq_ctn = parse_numeric(getattr(shipment, 'shipped_bq_ctn', 0))
            challan.shipped_aq_bails = parse_numeric(getattr(shipment, 'shipped_aq_bails', 0))
            challan.shipped_bq_bails = parse_numeric(getattr(shipment, 'shipped_bq_bails', 0))
            challan.shipped_packets = parse_numeric(shipment.shipped_packets)
            challan.shipped_ctn = parse_numeric(shipment.shipped_ctn)
            challan.shipped_bails = parse_numeric(shipment.shipped_bails)
            challan.shipped_by_party = shipment.shipped_by_party or 'Canon'
            continue
        order = Order.query.get(shipment.order_id)
        db.session.add(ChallanRecord(
            challan_no=next_challan_number(shipment.shipped_by_party or 'Canon'),
            source_type='order',
            shipment_id=shipment.id,
            order_id=shipment.order_id,
            job_no=shipment.job_no or (order.job_no if order else ''),
            party_name=order.name if order else '',
            article_name=(order.article_name or order.article) if order else '',
            challan_date=shipment.shipped_at or '',
            shipped_pcs=parse_numeric(shipment.shipped_pcs),
            shipped_aq_pcs=parse_numeric(getattr(shipment, 'shipped_aq_pcs', 0)),
            shipped_bq_pcs=parse_numeric(getattr(shipment, 'shipped_bq_pcs', 0)),
            shipped_aq_direct_pcs=parse_numeric(getattr(shipment, 'shipped_aq_direct_pcs', 0)),
            shipped_bq_direct_pcs=parse_numeric(getattr(shipment, 'shipped_bq_direct_pcs', 0)),
            shipped_aq_packets=parse_numeric(getattr(shipment, 'shipped_aq_packets', 0)),
            shipped_bq_packets=parse_numeric(getattr(shipment, 'shipped_bq_packets', 0)),
            shipped_aq_ctn=parse_numeric(getattr(shipment, 'shipped_aq_ctn', 0)),
            shipped_bq_ctn=parse_numeric(getattr(shipment, 'shipped_bq_ctn', 0)),
            shipped_aq_bails=parse_numeric(getattr(shipment, 'shipped_aq_bails', 0)),
            shipped_bq_bails=parse_numeric(getattr(shipment, 'shipped_bq_bails', 0)),
            shipped_packets=parse_numeric(shipment.shipped_packets),
            shipped_ctn=parse_numeric(shipment.shipped_ctn),
            shipped_bails=parse_numeric(shipment.shipped_bails),
            shipped_by_party=shipment.shipped_by_party or 'Canon',
            created_by=shipment.shipped_by or '',
        ))
        db.session.flush()

    for inventory in Inventory.query.filter_by(b_returned_to_party=True, b_returned_shipped=True).all():
        returned_meter = parse_numeric(inventory.b_returned_quantity)
        grouped_return = any(
            inventory.id in (json.loads(challan.combined_inventory_ids or '[]') if challan.combined_inventory_ids else [])
            for challan in ChallanRecord.query.filter_by(source_type='order').all()
        )
        if returned_meter <= 0 or grouped_return or ChallanRecord.query.filter_by(inventory_id=inventory.id, source_type='inventory_return').first():
            continue
        db.session.add(ChallanRecord(
            challan_no=next_challan_number(inventory.b_returned_shipped_by or 'Canon'),
            source_type='inventory_return',
            inventory_id=inventory.id,
            job_no=f"RETURNED-{inventory.serial_no or inventory.id}",
            party_name=inventory.b_returned_party or '',
            article_name=inventory.b_returned_article or inventory.fabric_for or '',
            challan_date=inventory.b_returned_date or inventory.recv_date or '',
            shipped_meter=returned_meter,
            shipped_by_party=inventory.b_returned_shipped_by or 'Canon',
            created_by=inventory.b_returned_by or '',
        ))
        db.session.flush()
    normalize_challan_number_sequences()
    db.session.commit()


class CostingSheetHistory(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    article_id = db.Column(db.Integer, db.ForeignKey('article.id'), nullable=False)
    created_by = db.Column(db.String(100))
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    snapshot_json = db.Column(db.Text, nullable=False)
    article = db.relationship('Article', backref=db.backref('costing_history', lazy=True, cascade='all, delete-orphan'))

class ProductionLog(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    date = db.Column(db.String(50))    
    job_no = db.Column(db.String(50))
    file_no = db.Column(db.String(50))
    party = db.Column(db.String(100))
    article = db.Column(db.String(100))
    article_name = db.Column(db.String(100))
    order_style = db.Column(db.String(100))
    worker = db.Column(db.String(100))
    operation = db.Column(db.String(100))
    pcs = db.Column(db.Integer)
    cut_pcs = db.Column(db.Integer)
    bq_unstitch = db.Column(db.Integer)
    bq_stitched = db.Column(db.Integer)
    color = db.Column(db.String(50))
    cut_no = db.Column(db.String(50))
    cut_size = db.Column(db.String(50))


class JobSheetAdditional(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    date = db.Column(db.String(50), nullable=False)
    worker = db.Column(db.String(100), nullable=False)
    party = db.Column(db.String(100))
    article_name = db.Column(db.String(100))
    order_style = db.Column(db.String(100))
    color = db.Column(db.String(50))
    file_no = db.Column(db.String(50))
    cut_no = db.Column(db.String(50))
    operation = db.Column(db.String(100))
    pcs = db.Column(db.Integer, default=0)
    rate = db.Column(db.Float, default=0.0)


class OperationRate(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    operation = db.Column(db.String(100), unique=True, nullable=False)
    rate = db.Column(db.Float, nullable=False)
    is_machine_operation = db.Column(db.Boolean, default=False, nullable=False)
    is_stitched_operation = db.Column(db.Boolean, default=False, nullable=False)
    is_special_operation = db.Column(db.Boolean, default=False, nullable=False)
    updated_at = db.Column(db.DateTime, default=datetime.utcnow)


class ArticleOperationRate(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    article_id = db.Column(db.Integer, db.ForeignKey('article.id'), nullable=False, index=True)
    rate_id = db.Column(db.Integer, db.ForeignKey('operation_rate.id'), nullable=False, index=True)
    override_rate = db.Column(db.Float)
    is_enabled = db.Column(db.Boolean, default=True, nullable=False)
    is_special_operation = db.Column(db.Boolean, default=False, nullable=False)
    sort_order = db.Column(db.Integer, default=0, nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    __table_args__ = (db.UniqueConstraint('article_id', 'rate_id', name='uq_article_operation_rate'),)


class ArticleOperationRateHistory(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    article_id = db.Column(db.Integer, db.ForeignKey('article.id'), nullable=False, index=True)
    rate_id = db.Column(db.Integer, db.ForeignKey('operation_rate.id'), nullable=False, index=True)
    override_rate = db.Column(db.Float)
    effective_date = db.Column(db.DateTime, nullable=False)
    portal_name = db.Column(db.String(150), default='', nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)


class OperationRateHistory(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    operation = db.Column(db.String(100), nullable=False, index=True)
    rate = db.Column(db.Float, nullable=False)
    effective_date = db.Column(db.DateTime, nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    order_id = db.Column(db.Integer, db.ForeignKey('order.id'), index=True)


class OrderOperationRate(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    order_id = db.Column(db.Integer, db.ForeignKey('order.id'), nullable=False, index=True)
    rate_id = db.Column(db.Integer, db.ForeignKey('operation_rate.id'), nullable=False, index=True)
    override_rate = db.Column(db.Float)
    sort_order = db.Column(db.Integer, default=0, nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    __table_args__ = (db.UniqueConstraint('order_id', 'rate_id', name='uq_order_operation_rate'),)


class CutSpecialOperation(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    order_id = db.Column(db.Integer, db.ForeignKey('order.id'), nullable=False, index=True)
    cut_no = db.Column(db.String(50), nullable=False)
    rate_id = db.Column(db.Integer, db.ForeignKey('operation_rate.id'), nullable=False, index=True)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    __table_args__ = (db.UniqueConstraint('order_id', 'cut_no', 'rate_id', name='uq_cut_special_operation'),)


def get_rate_for_operation_at(operation, date_str, order=None, article=None):
    """Return the effective rate for an operation, honoring saved overrides first.
    Falls back to historical/current general rates if no order or article override exists.
    """
    if not operation:
        return 0.0

    op = (operation or '').upper()
    rate_record = OperationRate.query.filter_by(operation=op).first()
    dt = normalize_date(date_str) or datetime.utcnow()

    if order is None and article is None and rate_record is None:
        return 0.0

    if order is None and article is None:
        order = None

    if order is not None and rate_record is not None:
        saved_order_rate = OrderOperationRate.query.filter_by(order_id=order.id, rate_id=rate_record.id).first()
        if saved_order_rate and saved_order_rate.override_rate is not None:
            return float(saved_order_rate.override_rate or 0.0)

    if order is not None and article is None:
        article = order.article_ref if order.article_ref else None
        if not article and order.article:
            article = Article.query.filter_by(article_no=normalize_article_no(order.article)).first()

    if article is not None and rate_record is not None:
        article_id = article.id if isinstance(article, Article) else article
        article_history = ArticleOperationRateHistory.query.filter_by(
            article_id=article_id,
            rate_id=rate_record.id,
        ).filter(
            ArticleOperationRateHistory.effective_date <= dt
        ).order_by(
            ArticleOperationRateHistory.effective_date.desc(),
            ArticleOperationRateHistory.id.desc(),
        ).first()
        if article_history:
            if article_history.override_rate is not None:
                return float(article_history.override_rate or 0.0)
        elif not ArticleOperationRateHistory.query.filter_by(
            article_id=article_id,
            rate_id=rate_record.id,
        ).first():
            saved_article_rate = ArticleOperationRate.query.filter_by(
                article_id=article_id,
                rate_id=rate_record.id,
            ).first()
            if saved_article_rate and saved_article_rate.override_rate is not None:
                return float(saved_article_rate.override_rate or 0.0)

    try:
        hist = OperationRateHistory.query.filter_by(operation=op).filter(OperationRateHistory.effective_date <= dt).order_by(OperationRateHistory.effective_date.desc()).first()
        if hist:
            return float(hist.rate or 0.0)
    except Exception:
        pass
    try:
        if rate_record:
            return float(rate_record.rate or 0.0)
    except Exception:
        pass
    return 0.0


def get_rate_for_log(log):
    if not log:
        return 0.0

    worker_name = (getattr(log, 'worker', None) or '').strip()
    worker = None
    if worker_name:
        worker = Worker.query.filter(
            func.lower(func.trim(Worker.name)) == worker_name.lower()
        ).first()
        employment_type = str(getattr(worker, 'employment_type', '') or '').strip().lower()
        employment_type = employment_type.replace('-', '_').replace(' ', '_')
        if (
            worker
            and str(getattr(worker, 'role', '') or '').strip().upper() == 'LABOUR'
            and employment_type in ('per_day', 'salaried')
        ):
            return 0.0

    order = None
    if getattr(log, 'job_no', None):
        order = Order.query.filter_by(job_no=log.job_no).first()

    article = None
    if order:
        article = order.article_ref if order.article_ref else None
        if not article and order.article:
            article = Article.query.filter_by(article_no=normalize_article_no(order.article)).first()
    elif getattr(log, 'article', None):
        article = Article.query.filter_by(article_no=normalize_article_no(log.article)).first()

    return get_rate_for_operation_at(log.operation, log.date, order=order, article=article)


def get_rates_dict():
    """Return a dict mapping operation names (uppercased) to float rates from DB."""
    rates = {}
    try:
        for r in OperationRate.query.all():
            key = (r.operation or '').upper()
            try:
                rates[key] = float(r.rate or 0.0)
            except Exception:
                rates[key] = 0.0
    except Exception:
        # DB might not be ready during early startup; fall back to empty dict
        pass
    return rates


def get_rates_for_article(article):
    """Return selected rates for an article, or all general rates if none are selected."""
    general_rates = get_rates_dict()
    if not article:
        return general_rates

    article_id = article.id if isinstance(article, Article) else article
    assignments = ArticleOperationRate.query.filter_by(article_id=article_id).all()
    special_rate_ids = {
        item.rate_id for item in assignments if item.is_special_operation
    }
    selected = (
        db.session.query(OperationRate, ArticleOperationRate.override_rate)
        .join(ArticleOperationRate, ArticleOperationRate.rate_id == OperationRate.id)
        .filter(
            ArticleOperationRate.article_id == article_id,
            ArticleOperationRate.is_enabled.is_(True),
            ArticleOperationRate.is_special_operation.is_(False),
        )
        .order_by(ArticleOperationRate.sort_order.asc(), ArticleOperationRate.id.asc())
        .all()
    )
    if not selected:
        special_names = {
            (rate.operation or '').upper()
            for rate in OperationRate.query.filter(OperationRate.id.in_(special_rate_ids)).all()
        } if special_rate_ids else set()
        return {
            operation: rate
            for operation, rate in general_rates.items()
            if operation not in special_names
        }
    return {
        (rate.operation or '').upper(): float(override if override is not None else rate.rate or 0.0)
        for rate, override in selected
    }


def get_rates_for_order(order):
    """Return an order's explicit rates, or inherit the article's rates."""
    if not order:
        return get_rates_dict()

    configured = OrderOperationRate.query.filter_by(order_id=order.id).order_by(
        OrderOperationRate.sort_order.asc(), OrderOperationRate.id.asc()
    ).all()
    if not configured:
        article = order.article_ref if order.article_ref else None
        if not article and order.article:
            article = Article.query.filter_by(article_no=normalize_article_no(order.article)).first()
        return get_rates_for_article(article)

    rate_ids = [item.rate_id for item in configured]
    rates = {rate.id: rate for rate in OperationRate.query.filter(OperationRate.id.in_(rate_ids)).all()}
    return {
        (rates[item.rate_id].operation or '').upper(): float(
            item.override_rate if item.override_rate is not None else rates[item.rate_id].rate or 0.0
        )
        for item in configured
        if item.rate_id in rates
    }


def get_article_for_order(order):
    if not order:
        return None
    article = order.article_ref if order.article_ref else None
    if not article and order.article:
        article = Article.query.filter_by(article_no=normalize_article_no(order.article)).first()
    return article


def get_article_special_assignments(article):
    if not article:
        return []
    article_id = article.id if isinstance(article, Article) else article
    return ArticleOperationRate.query.filter_by(
        article_id=article_id,
        is_special_operation=True,
    ).order_by(ArticleOperationRate.sort_order.asc(), ArticleOperationRate.id.asc()).all()


def get_special_operations_for_cut(order, cut_no):
    if not order or cut_no is None:
        return []
    article_special_assignments = get_article_special_assignments(get_article_for_order(order))
    special_rate_ids = {item.rate_id for item in article_special_assignments}
    if not special_rate_ids:
        return []
    selected_rate_ids = [rate_id for (rate_id,) in db.session.query(
        CutSpecialOperation.rate_id
    ).filter_by(
        order_id=order.id,
        cut_no=str(cut_no),
    ).all()]
    selected_rate_ids = special_rate_ids.intersection(selected_rate_ids)
    if not selected_rate_ids:
        return []
    return OperationRate.query.filter(
        OperationRate.id.in_(selected_rate_ids),
    ).order_by(OperationRate.operation.asc()).all()


def get_rates_for_cut(order, cut_no):
    order_rates = get_rates_for_order(order)
    article_special_assignments = get_article_special_assignments(get_article_for_order(order))
    special_rate_ids = {item.rate_id for item in article_special_assignments}
    special_rates_by_id = {
        rate.id: rate
        for rate in OperationRate.query.filter(OperationRate.id.in_(special_rate_ids)).all()
    } if special_rate_ids else {}
    special_names = {
        (rate.operation or '').upper() for rate in special_rates_by_id.values()
    }
    rates = {
        operation: rate
        for operation, rate in order_rates.items()
        if operation.upper() not in special_names
    }
    assignments_by_rate_id = {item.rate_id: item for item in article_special_assignments}
    for rate in get_special_operations_for_cut(order, cut_no):
        operation = (rate.operation or '').upper()
        assignment = assignments_by_rate_id.get(rate.id)
        rates[operation] = order_rates.get(
            operation,
            float(assignment.override_rate if assignment and assignment.override_rate is not None else rate.rate or 0.0),
        )
    return rates


def get_machine_operations(operation_names):
    names = [str(name).upper() for name in operation_names if name]
    if not names:
        return {}
    rates = OperationRate.query.filter(
        func.upper(OperationRate.operation).in_(names)
    ).all()
    return {
        (rate.operation or '').upper(): bool(rate.is_machine_operation)
        for rate in rates
    }


def get_cut_production_state(job_no, cut_no, base_limit, operation_names, logs=None):
    """Calculate raw B/Q totals and the effective limit for every operation."""
    if logs is None:
        logs = ProductionLog.query.filter_by(job_no=job_no, cut_no=cut_no).all()

    machine_operations = get_machine_operations(operation_names)
    raw_totals = {operation: 0 for operation in operation_names}
    bq_totals = {operation: 0 for operation in operation_names}
    stitched_bq_totals = {operation: 0 for operation in operation_names}
    machine_bq_totals = {operation: 0 for operation in operation_names}
    for log in logs:
        operation = (log.operation or '').upper()
        if operation not in raw_totals:
            continue
        raw_totals[operation] += max(0, int(log.pcs or 0))
        bq_unstitch = max(0, int(log.bq_unstitch or 0))
        bq_stitched = max(0, int(log.bq_stitched or 0))
        if machine_operations.get(operation):
            bq_totals[operation] += bq_unstitch
            machine_bq_totals[operation] += bq_unstitch
        else:
            bq_totals[operation] += bq_unstitch
        # Stitched B/Q does not reduce the inline PCS that was issued by the
        # last unstitched operation. It is validated against that inline amount
        # instead of being deducted from the remaining capacity.
        stitched_bq_totals[operation] += bq_stitched

    limits_before_bq = {}
    effective_limits = {}
    credited_totals = {
        operation: max(0, raw_totals[operation] - bq_totals[operation])
        for operation in operation_names
    }
    remaining_limit = max(0, int(base_limit or 0))
    for operation in operation_names:
        limits_before_bq[operation] = remaining_limit
        effective_limits[operation] = max(0, remaining_limit - bq_totals[operation])
        remaining_limit = effective_limits[operation]

    # A machine defect found later applies the same reduced limit to every
    # earlier machine operation, preventing additional entries there.
    for operation_index, operation in enumerate(operation_names):
        if not machine_operations.get(operation) or not machine_bq_totals[operation]:
            continue
        propagated_limit = effective_limits[operation]
        for previous_operation in operation_names[:operation_index]:
            if not machine_operations.get(previous_operation):
                continue
            effective_limits[previous_operation] = min(
                effective_limits[previous_operation],
                propagated_limit,
            )

    return {
        'machine_operations': machine_operations,
        'raw_totals': raw_totals,
        'bq_totals': bq_totals,
        'stitched_bq_totals': stitched_bq_totals,
        'machine_bq_totals': machine_bq_totals,
        'limits_before_bq': limits_before_bq,
        'effective_limits': effective_limits,
        'credited_totals': credited_totals,
    }


def deduct_previous_operation_pieces(job_no, cut_no, operation, amount):
    """Remove machine-detected defects proportionally from an operation's logs."""
    remaining = max(0, int(amount or 0))
    if remaining <= 0:
        return
    previous_logs = ProductionLog.query.filter_by(
        job_no=job_no,
        cut_no=cut_no,
        operation=operation,
    ).order_by(ProductionLog.id.asc()).all()
    total_pcs = sum(max(0, int(log.pcs or 0)) for log in previous_logs)
    if remaining > total_pcs:
        raise ValueError(
            f'B/Q Un-stitch cannot exceed the available {operation} production.'
        )

    allocated = 0
    for index, log in enumerate(previous_logs):
        worker_pcs = max(0, int(log.pcs or 0))
        if index == len(previous_logs) - 1:
            deduction = remaining - allocated
        else:
            deduction = int(round(remaining * worker_pcs / total_pcs)) if total_pcs else 0
            deduction = min(deduction, worker_pcs)
        log.pcs = max(0, worker_pcs - deduction)
        allocated += deduction


def deduct_previous_machine_operation_pieces(
    job_no,
    cut_no,
    operation_names,
    current_operation_index,
    machine_operations,
    amount,
):
    """Remove the same machine-detected B/Q amount from every earlier machine operation."""
    for operation in operation_names[:current_operation_index]:
        if machine_operations.get(operation):
            deduct_previous_operation_pieces(job_no, cut_no, operation, amount)


def get_worker_advance_summary(worker_name):
    """Return outstanding advances and their entries for a worker name."""
    if not worker_name:
        return 0.0, []

    worker = Worker.query.filter(
        func.lower(func.trim(Worker.name)) == str(worker_name).strip().lower()
    ).first()
    if not worker:
        return 0.0, []

    entries = WorkerAdvance.query.filter_by(worker_id=worker.id).order_by(
        WorkerAdvance.date.asc(), WorkerAdvance.id.asc()
    ).all()
    total = sum(
        float(entry.amount or 0.0) if entry.record_type == 'advance' else -float(entry.amount or 0.0)
        for entry in entries
    )
    return max(0.0, total), entries

class Worker(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(100))
    email = db.Column(db.String(100))
    phone = db.Column(db.String(50))
    whatsapp_number = db.Column(db.String(50))
    emergency_number = db.Column(db.String(50))
    blood_group = db.Column(db.String(20))
    picture = db.Column(db.String(255))
    age = db.Column(db.Integer)
    worker_code = db.Column(db.String(50))
    cnic = db.Column(db.String(50))
    role = db.Column(db.String(50))
    dob = db.Column(db.String(50))
    gender = db.Column(db.String(20))
    marital_status = db.Column(db.String(50))
    nationality = db.Column(db.String(100))
    address = db.Column(db.String(255))
    city = db.Column(db.String(100))
    state = db.Column(db.String(100))
    zip_code = db.Column(db.String(50))
    supervisor = db.Column(db.String(100))
    sub_designation = db.Column(db.String(100))
    joining_date = db.Column(db.String(50))
    referred_by = db.Column(db.String(100))
    hired_by = db.Column(db.String(100))
    salary = db.Column(db.Float)
    attendance_allowance = db.Column(db.Float)
    hod = db.Column(db.String(100))
    employment_type = db.Column(db.String(50))
    department = db.Column(db.String(100))
    status = db.Column(db.String(20), nullable=False, default='Active')
    education_entries = db.relationship('EducationBackground', backref='worker', cascade='all, delete-orphan')
    advances = db.relationship('WorkerAdvance', backref='worker', cascade='all, delete-orphan')

class Department(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    name = db.Column(db.String(100), unique=True, nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    store_rooms = db.relationship(
        'DepartmentStoreRoom',
        backref='department',
        cascade='all, delete-orphan',
        lazy=True,
        order_by='DepartmentStoreRoom.name',
    )


class DepartmentStoreRoom(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    department_id = db.Column(
        db.Integer,
        db.ForeignKey('department.id', ondelete='CASCADE'),
        nullable=False,
        index=True,
    )
    name = db.Column(db.String(100), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    __table_args__ = (
        db.UniqueConstraint('department_id', 'name', name='uq_department_store_room'),
    )

class EducationBackground(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    worker_id = db.Column(db.Integer, db.ForeignKey('worker.id', ondelete='CASCADE'))
    degree = db.Column(db.String(255))
    field_of_study = db.Column(db.String(255))
    institution = db.Column(db.String(255))
    completion_date = db.Column(db.String(50))

class WorkerAdvance(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    worker_id = db.Column(db.Integer, db.ForeignKey('worker.id', ondelete='CASCADE'))
    amount = db.Column(db.Float)
    date = db.Column(db.String(50))
    record_type = db.Column(db.String(20))  # advance or payment
    note = db.Column(db.String(255))
    is_paid = db.Column(db.Boolean, default=False, nullable=False)
    paid_period = db.Column(db.String(80))
    paid_at = db.Column(db.DateTime)


class SalaryPayment(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    worker_id = db.Column(db.Integer, db.ForeignKey('worker.id', ondelete='CASCADE'))
    department = db.Column(db.String(100))
    payout_portal = db.Column(db.String(50))
    company = db.Column(db.String(30), nullable=False, default='Canon')
    period_type = db.Column(db.String(30))
    period_label = db.Column(db.String(120))
    period_start = db.Column(db.String(20))
    period_end = db.Column(db.String(20))
    amount = db.Column(db.Float, default=0.0)
    paid_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class Attendance(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    worker_id = db.Column(db.Integer, db.ForeignKey('worker.id', ondelete='CASCADE'), nullable=False, index=True)
    year = db.Column(db.Integer, nullable=False, index=True)
    month = db.Column(db.Integer, nullable=False, index=True)
    factory_operating_days = db.Column(db.Integer, nullable=False)
    absent_days = db.Column(db.Integer, nullable=False)
    present_days = db.Column(db.Integer, nullable=False)
    overtime_hours = db.Column(db.Float, nullable=False, default=0.0)
    early_leave_hours = db.Column(db.Float, nullable=False, default=0.0)
    night_hours = db.Column(db.Float, nullable=False, default=0.0)
    late_days = db.Column(db.Integer, nullable=False, default=0)
    on_time_days = db.Column(db.Integer, nullable=False, default=0)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    updated_at = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow, nullable=False)
    __table_args__ = (db.UniqueConstraint('worker_id', 'year', 'month', name='uq_attendance_worker_year_month'),)

class DailyAttendance(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    worker_id = db.Column(db.Integer, db.ForeignKey('worker.id', ondelete='CASCADE'), nullable=False, index=True)
    date = db.Column(db.String(10), nullable=False, index=True)
    status = db.Column(db.String(1), nullable=False, default='P')
    late_hours = db.Column(db.Float, nullable=False, default=0.0)
    early_hours = db.Column(db.Float, nullable=False, default=0.0)
    overtime_hours = db.Column(db.Float, nullable=False, default=0.0)
    night_hours = db.Column(db.Float, nullable=False, default=0.0)
    __table_args__ = (db.UniqueConstraint('worker_id', 'date', name='uq_daily_attendance_worker_date'),)

class Inventory(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    serial_no = db.Column(db.String(100), unique=True)
    order_id = db.Column(db.String(100))
    recv_date = db.Column(db.String(50))
    received_from = db.Column(db.String(100))
    suppliers = db.Column("suppliers", db.String(100))
    challan_no = db.Column(db.String(100))
    place = db.Column(db.String(100))
    meter_note = db.Column(db.String(100))
    ms = db.Column(db.String(100))
    file_no = db.Column(db.String(100))
    fabric_qty_a = db.Column(db.String(50))
    fabric_qty_b = db.Column(db.String(50))
    fabric_b_enabled = db.Column(db.Boolean, nullable=False, default=False)
    fabric_b_activation_cut_no = db.Column(db.Integer)
    fabric_b_activation_order_id = db.Column(db.String(100))
    fabric_quality = db.Column(db.String(100))
    cut_size_header = db.Column(db.String(100))
    width = db.Column(db.String(100))
    req_cutting = db.Column(db.String(100))
    receive_cut_pcs = db.Column(db.String(50))
    fabric_for = db.Column(db.String(100))
    consumption = db.Column(db.String(100))
    req_average = db.Column(db.String(100))
    total = db.Column(db.String(100))
    used_fabric = db.Column(db.String(100))
    left_over_fabric = db.Column(db.String(100))
    rejected_fabric = db.Column(db.String(100))
    rejected_recovered_fabric = db.Column(db.String(100), default='0.00')
    rejected_recovered_removed_at = db.Column(db.String(50), default='')
    a_returned_to_party = db.Column(db.Boolean, nullable=False, default=False)
    a_returned_quantity = db.Column(db.String(50), default='0.00')
    a_returned_date = db.Column(db.String(50), default='')
    a_returned_by = db.Column(db.String(100), default='')
    a_returned_party = db.Column(db.String(200), default='')
    a_returned_article = db.Column(db.String(200), default='')
    a_returned_shipped = db.Column(db.Boolean, nullable=False, default=False)
    a_returned_shipped_by = db.Column(db.String(100), default='')
    a_returned_shipped_date = db.Column(db.String(50), default='')
    b_returned_to_party = db.Column(db.Boolean, nullable=False, default=False)
    b_returned_quantity = db.Column(db.String(50), default='0.00')
    b_returned_date = db.Column(db.String(50), default='')
    b_returned_by = db.Column(db.String(100), default='')
    b_returned_party = db.Column(db.String(200), default='')
    b_returned_article = db.Column(db.String(200), default='')
    b_returned_shipped = db.Column(db.Boolean, nullable=False, default=False)
    b_returned_shipped_by = db.Column(db.String(100), default='')
    b_returned_shipped_date = db.Column(db.String(50), default='')
    item_name = db.Column(db.String(100))
    quantity = db.Column(db.Integer)
    unit = db.Column(db.String(20))
    rows = db.relationship('InventoryRow', backref='inventory', cascade='all, delete-orphan')
    second_rows = db.relationship('InventorySecondRow', backref='inventory', cascade='all, delete-orphan')


class InventoryRow(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    inventory_id = db.Column(db.Integer, db.ForeignKey('inventory.id', ondelete='CASCADE'))
    idx = db.Column(db.Integer)
    date = db.Column(db.String(50))
    item = db.Column(db.String(200))
    sno = db.Column(db.String(100))
    file_no = db.Column(db.String(100))
    cut_no = db.Column(db.String(100))
    cut_size = db.Column(db.String(100))
    cutting_pcs = db.Column(db.Integer)
    fabric_req = db.Column(db.String(50))
    fabric_issue = db.Column(db.String(50))
    issue_by = db.Column(db.String(100))
    fabric_return = db.Column(db.String(50))
    fabric_use = db.Column(db.String(50))
    wastage = db.Column(db.String(50))
    cut_pcs = db.Column(db.Integer)
    balance = db.Column(db.String(50))


class InventorySecondRow(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    inventory_id = db.Column(db.Integer, db.ForeignKey('inventory.id', ondelete='CASCADE'))
    idx = db.Column(db.Integer)
    style = db.Column(db.String(200))
    sno = db.Column(db.String(100))
    cut_size = db.Column(db.String(100))
    cutting_pcs = db.Column(db.Integer)
    fabric_use = db.Column(db.String(50))
    cut_pcs = db.Column(db.Integer)
    shortage = db.Column(db.String(50))
    balance = db.Column(db.String(50))

class ReceivingChallan(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    order_id = db.Column(db.String(100))
    serial_no = db.Column(db.String(100))
    recv_date = db.Column(db.String(50))
    suppliers = db.Column("suppliers", db.String(100))
    challan_no = db.Column(db.String(100))
    fabric_quality = db.Column(db.String(100))
    width = db.Column(db.String(100))
    fabric_for = db.Column(db.String(100))
    used_file_no = db.Column(db.String(100))
    place = db.Column(db.String(100))
    reciever_name = db.Column(db.String(100))
    per_dozen_consumption = db.Column(db.String(50))
    required_ctn_bails = db.Column(db.String(50))
    received_from = db.Column(db.String(100))
    meter_to_cm = db.Column(db.String(50))
    fabric_qty_a = db.Column(db.String(50))
    fabric_qty_b = db.Column(db.String(50))
    received_cut_pcs = db.Column(db.String(50))
    total = db.Column(db.String(50))
    rolls = db.Column(db.String(50))
    vehicle_no = db.Column(db.String(100))
    delivered_by = db.Column(db.String(100))
    driver_cell_no = db.Column(db.String(50))
    image_file = db.Column(db.String(255))
    created_at = db.Column(db.DateTime, default=datetime.utcnow)


class FactoryManualMovement(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    date = db.Column(db.String(10), nullable=False, index=True)
    direction = db.Column(db.String(3), nullable=False, index=True)
    item = db.Column(db.String(200), nullable=False)
    description = db.Column(db.String(500), default='')
    reference = db.Column(db.String(100), default='')
    quantity = db.Column(db.Float, nullable=False)
    unit = db.Column(db.String(20), nullable=False)
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class PartySuppliedAccessory(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    sent_date = db.Column(db.String(10), nullable=False, index=True)
    order_id = db.Column(db.String(100), nullable=False, index=True)
    party_name = db.Column(db.String(200), default='')
    article_name = db.Column(db.String(200), default='')
    item = db.Column(db.String(255), nullable=False)
    size = db.Column(db.String(100), default='')
    quality = db.Column(db.String(100), default='')
    quantity = db.Column(db.Float, nullable=False)
    unit = db.Column(db.String(50), nullable=False, default='PCS')
    note = db.Column(db.String(500), default='')
    recorded_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)


class SavedRequirement(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    serial_no = db.Column(db.String(50))
    order_id = db.Column(db.String(100))
    item = db.Column(db.String(255))
    qty = db.Column(db.String(50))
    size = db.Column(db.String(100))
    unit = db.Column(db.String(50), default='')
    roll_length_m = db.Column(db.Float, nullable=False, default=0.0)
    issue_unit = db.Column(db.String(50), default='')
    issue_unit_factor = db.Column(db.Float, nullable=False, default=1.0)
    quality = db.Column(db.String(100))
    rate = db.Column(db.String(100))
    bill_amount = db.Column(db.String(100))
    supplier = db.Column(db.String(200))
    requested_by = db.Column(db.String(100))
    priority = db.Column(db.String(50))
    date = db.Column(db.String(50))
    for_field = db.Column(db.String(100))
    po_no = db.Column(db.String(100))
    accessory_status = db.Column(db.String(30), default='PENDING')
    received_qty = db.Column(db.String(50), default='0')
    issued_qty = db.Column(db.String(50), default='0')
    used_qty = db.Column(db.String(50), default='0')
    po_sent_at = db.Column(db.String(50))
    purchase_slip_image = db.Column(db.String(255))
    received_at = db.Column(db.String(50))
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    issue_entries = db.relationship('AccessoryIssue', backref='requirement', cascade='all, delete-orphan', lazy=True)


class AccessoryIssue(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    requirement_id = db.Column(db.Integer, db.ForeignKey('saved_requirement.id'), nullable=False, index=True)
    storage_location_id = db.Column(db.Integer, db.ForeignKey('accessory_storage_location.id', ondelete='SET NULL'), index=True)
    order_id = db.Column(db.String(100))
    cut_no = db.Column(db.String(50))
    cut_sheet_id = db.Column(db.Integer, db.ForeignKey('cutting_sheet.id', ondelete='SET NULL'), index=True)
    cutting_pcs = db.Column(db.Float)
    issue_date = db.Column(db.String(50), nullable=False)
    worker_name = db.Column(db.String(150), nullable=False)
    issued_qty = db.Column(db.Float, nullable=False, default=0.0)
    issued_as_qty = db.Column(db.Float, nullable=False, default=0.0)
    issued_as_unit = db.Column(db.String(50), default='')
    issue_conversion_factor = db.Column(db.Float, nullable=False, default=1.0)
    unit_rate = db.Column(db.Float, nullable=False, default=0.0)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    return_entries = db.relationship('AccessoryReturn', back_populates='issue', lazy=True)


class AccessoryStorageLocation(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    requirement_id = db.Column(db.Integer, db.ForeignKey('saved_requirement.id'), nullable=False, index=True)
    location_type = db.Column(db.String(20), nullable=False)
    department = db.Column(db.String(100), nullable=False, default='')
    gala = db.Column(db.String(100), nullable=False, default='')
    room = db.Column(db.String(100), nullable=False, default='Store Room')
    rack_no = db.Column(db.String(50), default='')
    shelf_no = db.Column(db.String(50), default='')
    carton_no = db.Column(db.String(50), default='')
    description = db.Column(db.String(200), default='')
    quantity = db.Column(db.Float, nullable=False, default=0.0)
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    requirement = db.relationship('SavedRequirement', backref=db.backref('storage_locations', lazy=True))
    issue_entries = db.relationship('AccessoryIssue', backref='storage_location', lazy=True)


class AccessoryReturn(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    issue_id = db.Column(db.Integer, db.ForeignKey('accessory_issue.id'), nullable=False, index=True)
    return_date = db.Column(db.String(50), nullable=False)
    returned_by = db.Column(db.String(150), nullable=False)
    returned_qty = db.Column(db.Float, nullable=False)
    note = db.Column(db.String(255), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    issue = db.relationship('AccessoryIssue', back_populates='return_entries')


class AccessorySupplierReturn(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    requirement_id = db.Column(
        db.Integer,
        db.ForeignKey('saved_requirement.id', ondelete='CASCADE'),
        nullable=False,
        index=True,
    )
    storage_location_id = db.Column(
        db.Integer,
        db.ForeignKey('accessory_storage_location.id', ondelete='SET NULL'),
        index=True,
    )
    return_date = db.Column(db.String(10), nullable=False)
    returned_by = db.Column(db.String(150), nullable=False)
    return_type = db.Column(db.String(20), nullable=False, default='RETURN')
    returned_qty = db.Column(db.Float, nullable=False)
    unit_rate = db.Column(db.Float, nullable=False, default=0.0)
    exchange_item = db.Column(db.String(150), default='')
    exchange_item_unit = db.Column(db.String(50), default='')
    note = db.Column(db.String(255), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    requirement = db.relationship(
        'SavedRequirement',
        backref=db.backref('supplier_returns', cascade='all, delete-orphan', lazy=True),
    )
    storage_location = db.relationship('AccessoryStorageLocation')

class CuttingSheet(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    order_id = db.Column(db.String(100))
    cut_no = db.Column(db.String(50))
    serial_no = db.Column(db.String(50))
    cut_size = db.Column(db.String(100))
    factor_1 = db.Column(db.String(100))
    factor_2 = db.Column(db.String(100))
    total = db.Column(db.String(100))
    divisor = db.Column(db.String(100))
    result = db.Column(db.String(100))
    range_width = db.Column(db.String(100))
    range_height = db.Column(db.String(100))
    range_area = db.Column(db.String(100))
    pcs_in_row = db.Column(db.String(100))
    range_margin = db.Column(db.String(100))
    range_result = db.Column(db.String(100))
    pcs_in_range = db.Column(db.String(100))
    avg_99 = db.Column(db.String(100))
    avg_100 = db.Column(db.String(100))
    avg_other = db.Column(db.String(100))
    cutter_name = db.Column(db.String(200))
    fabric_issue = db.Column(db.String(100))
    inventory_serial_no = db.Column(db.String(100))
    use_fabric_ch = db.Column(db.String(100))
    asst_cutter_name = db.Column(db.String(200))
    palla_check_by = db.Column(db.String(200))
    bq_unstitch = db.Column(db.String(100))
    shortage = db.Column(db.String(50))
    summary_total_pcs = db.Column(db.String(100))
    summary_avg_pcs = db.Column(db.String(100))
    balance_cutting = db.Column(db.String(100))
    total_cutting = db.Column(db.String(100))
    to_date_production = db.Column(db.String(100))
    shift_to_next_cut = db.Column(db.String(100))
    remarks = db.Column(db.String(500))
    issued_by = db.Column(db.String(200))
    department = db.Column(db.String(200))
    bundle = db.Column(db.String(100))
    quantity = db.Column(db.String(100))
    issue_to_sv = db.Column(db.String(200))
    cut_date = db.Column(db.String(100))
    issue_date = db.Column(db.String(100))
    time_field = db.Column(db.String(100))
    balance_fabric = db.Column(db.String(100))
    fabric_meter = db.Column(db.String(100))
    total_meter = db.Column(db.String(100))
    total_palla = db.Column(db.String(100))
    total_pcs = db.Column(db.String(100))
    mini_palla_22 = db.Column(db.String(100))
    mini_pcs_22 = db.Column(db.String(100))
    mini_cp_22 = db.Column(db.String(100))
    mini_palla_22_grey = db.Column(db.String(100))
    mini_pcs_22_grey = db.Column(db.String(100))
    mini_cp_22_grey = db.Column(db.String(100))
    recovered_fabric_usage = db.Column(db.String(500), default='{}')
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    rows = db.relationship('CuttingSheetRow', backref='cutting_sheet', cascade='all, delete-orphan')
    bundle_stickers = db.relationship(
        'BundleStickerEntry',
        backref='cutting_sheet',
        cascade='all, delete-orphan',
        order_by='BundleStickerEntry.bundle_number',
    )

class CuttingSheetRow(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    cutting_sheet_id = db.Column(db.Integer, db.ForeignKey('cutting_sheet.id', ondelete='CASCADE'))
    idx = db.Column(db.Integer)
    meter = db.Column(db.String(100))
    palla = db.Column(db.String(100))
    pcs = db.Column(db.String(100))
    cp = db.Column(db.String(100))


class BundleStickerEntry(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    cutting_sheet_id = db.Column(
        db.Integer,
        db.ForeignKey('cutting_sheet.id', ondelete='CASCADE'),
        nullable=False,
        index=True,
    )
    bundle_number = db.Column(db.Integer, nullable=False)
    pcs = db.Column(db.Integer, nullable=False)
    __table_args__ = (
        db.UniqueConstraint('cutting_sheet_id', 'bundle_number', name='uq_bundle_sticker_number'),
    )


class CuttingTransfer(db.Model):
    __tablename__ = 'cutting_excess_transfer'

    id = db.Column(db.Integer, primary_key=True)
    source_order_id = db.Column(db.Integer, db.ForeignKey('order.id'), nullable=False, index=True)
    source_cutting_sheet_id = db.Column(
        'source_sheet_id',
        db.Integer,
        db.ForeignKey('cutting_sheet.id', ondelete='RESTRICT'),
        nullable=False,
        index=True,
    )
    source_job_no = db.Column(db.String(100), nullable=False)
    source_cut_no = db.Column(db.String(50), nullable=False)
    destination_order_id = db.Column(db.Integer, db.ForeignKey('order.id'), nullable=False, index=True)
    destination_cutting_sheet_id = db.Column(
        'destination_sheet_id',
        db.Integer,
        db.ForeignKey('cutting_sheet.id', ondelete='SET NULL'),
        nullable=True,
        index=True,
    )
    destination_job_no = db.Column(db.String(100), nullable=False)
    destination_cut_no = db.Column(db.String(50), nullable=False)
    quantity = db.Column('pcs', db.Integer, nullable=False)
    notes = db.Column(db.String(500), default='')
    request_token = db.Column(db.String(64), nullable=False, unique=True, default=lambda: os.urandom(24).hex())
    reversed_at = db.Column(db.DateTime)
    reversed_by = db.Column(db.String(100))
    created_by = db.Column(db.String(100), default='')
    created_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    source_cutting_sheet = db.relationship(
        'CuttingSheet',
        foreign_keys=[source_cutting_sheet_id],
        backref=db.backref('outgoing_transfers', lazy=True),
    )
    destination_cutting_sheet = db.relationship(
        'CuttingSheet',
        foreign_keys=[destination_cutting_sheet_id],
        backref=db.backref('incoming_transfers', lazy=True),
    )


def get_cutting_transfer_state(order, cutting_sheet, ordered_sheets=None):
    sheets = ordered_sheets
    if sheets is None:
        sheets = CuttingSheet.query.filter_by(order_id=order.job_no).all()
    sequence = sorted(
        sheets,
        key=lambda sheet: (
            int(str(sheet.cut_no)) if str(sheet.cut_no).isdigit() else 999999,
            sheet.id,
        ),
    )
    previous_cutting = 0.0
    for sheet in sequence:
        if sheet.id == cutting_sheet.id:
            break
        previous_cutting += parse_numeric(sheet.quantity)

    cutting_pcs = max(0.0, parse_numeric(cutting_sheet.quantity))
    remaining_required = max(get_effective_order_quantity(order) - previous_cutting, 0.0)
    required_portion = min(cutting_pcs, remaining_required)
    excess_pcs = max(cutting_pcs - required_portion, 0.0)
    transfers = CuttingTransfer.query.filter_by(
        source_cutting_sheet_id=cutting_sheet.id,
        reversed_at=None,
    ).order_by(CuttingTransfer.created_at.asc(), CuttingTransfer.id.asc()).all()
    transferred_pcs = sum(transfer.quantity for transfer in transfers)
    remaining_transferable = max(0, int(excess_pcs - transferred_pcs))

    return {
        'cutting_pcs': int(cutting_pcs),
        'required_portion': int(required_portion),
        'excess_pcs': int(excess_pcs),
        'transferred_pcs': transferred_pcs,
        'remaining_transferable': remaining_transferable,
        'transfers': transfers,
    }


class AnnualReport(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    year = db.Column(db.Integer, unique=True, nullable=False, index=True)
    reporting_period = db.Column(db.String(100), nullable=False)
    snapshot_json = db.Column(db.Text, nullable=False, default='{}')
    management_message = db.Column(db.Text, default='')
    major_achievements = db.Column(db.Text, default='')
    major_challenges = db.Column(db.Text, default='')
    future_plans = db.Column(db.Text, default='')
    additional_notes = db.Column(db.Text, default='')
    generated_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    finalized_at = db.Column(db.DateTime)
    generated_by = db.Column(db.String(100))
    finalized_by = db.Column(db.String(100))
    status = db.Column(db.String(20), default='Generated', nullable=False)

# Ensure DB has the new columns (best-effort, harmless if already present)
def ensure_table_columns(engine):
    try:
        inspector = inspect(engine)
        columns = {c['name'] for c in inspector.get_columns('cutting_sheet')}
        alter_sql = {
            'mini_palla_22': 'ALTER TABLE cutting_sheet ADD COLUMN mini_palla_22 VARCHAR(100)',
            'mini_pcs_22': 'ALTER TABLE cutting_sheet ADD COLUMN mini_pcs_22 VARCHAR(100)',
            'mini_cp_22': 'ALTER TABLE cutting_sheet ADD COLUMN mini_cp_22 VARCHAR(100)',
            'mini_palla_22_grey': 'ALTER TABLE cutting_sheet ADD COLUMN mini_palla_22_grey VARCHAR(100)',
            'mini_pcs_22_grey': 'ALTER TABLE cutting_sheet ADD COLUMN mini_pcs_22_grey VARCHAR(100)',
            'mini_cp_22_grey': 'ALTER TABLE cutting_sheet ADD COLUMN mini_cp_22_grey VARCHAR(100)',
            'pcs_in_row': 'ALTER TABLE cutting_sheet ADD COLUMN pcs_in_row VARCHAR(100)',
            'range_margin': 'ALTER TABLE cutting_sheet ADD COLUMN range_margin VARCHAR(100)',
            'range_result': 'ALTER TABLE cutting_sheet ADD COLUMN range_result VARCHAR(100)',
            'pcs_in_range': 'ALTER TABLE cutting_sheet ADD COLUMN pcs_in_range VARCHAR(100)',
            'fabric_issue': 'ALTER TABLE cutting_sheet ADD COLUMN fabric_issue VARCHAR(100)',
            'recovered_fabric_usage': "ALTER TABLE cutting_sheet ADD COLUMN recovered_fabric_usage VARCHAR(500) DEFAULT '{}'",
        }
        with engine.begin() as conn:
            for col, sql in alter_sql.items():
                if col not in columns:
                    try:
                        conn.execute(text(sql))
                    except Exception:
                        pass
        if 'customer_bill' in inspector.get_table_names():
            bill_columns = {column['name'] for column in inspector.get_columns('customer_bill')}
            with engine.begin() as conn:
                if 'customer_address' not in bill_columns:
                    conn.execute(text("ALTER TABLE customer_bill ADD COLUMN customer_address VARCHAR(255) NOT NULL DEFAULT ''"))
                if 'customer_phone' not in bill_columns:
                    conn.execute(text("ALTER TABLE customer_bill ADD COLUMN customer_phone VARCHAR(50) NOT NULL DEFAULT ''"))
                if 'further_tax_rate' not in bill_columns:
                    conn.execute(text("ALTER TABLE customer_bill ADD COLUMN further_tax_rate FLOAT NOT NULL DEFAULT 0"))
                if 'further_tax_amount' not in bill_columns:
                    conn.execute(text("ALTER TABLE customer_bill ADD COLUMN further_tax_amount FLOAT NOT NULL DEFAULT 0"))
        if 'billing_invoice' in inspector.get_table_names():
            invoice_columns = {column['name'] for column in inspector.get_columns('billing_invoice')}
            with engine.begin() as conn:
                for column_name, column_def in {
                    'party_address': "ALTER TABLE billing_invoice ADD COLUMN party_address VARCHAR(255) DEFAULT ''",
                    'party_city': "ALTER TABLE billing_invoice ADD COLUMN party_city VARCHAR(100) DEFAULT ''",
                    'party_ntn': "ALTER TABLE billing_invoice ADD COLUMN party_ntn VARCHAR(50) DEFAULT ''",
                    'sales_tax_no': "ALTER TABLE billing_invoice ADD COLUMN sales_tax_no VARCHAR(50) DEFAULT ''",
                    'further_tax_rate': "ALTER TABLE billing_invoice ADD COLUMN further_tax_rate FLOAT NOT NULL DEFAULT 0",
                    'further_tax_amount': "ALTER TABLE billing_invoice ADD COLUMN further_tax_amount FLOAT NOT NULL DEFAULT 0",
                }.items():
                    if column_name not in invoice_columns:
                        conn.execute(text(column_def))
        if 'utility_bill_summary' in inspector.get_table_names():
            summary_columns = {column['name'] for column in inspector.get_columns('utility_bill_summary')}
            summary_column_migrations = {
                'cheque_image': "ALTER TABLE utility_bill_summary ADD COLUMN cheque_image VARCHAR(255) NOT NULL DEFAULT ''",
                'bank_name': "ALTER TABLE utility_bill_summary ADD COLUMN bank_name VARCHAR(100) NOT NULL DEFAULT ''",
            }
            for column_name, migration in summary_column_migrations.items():
                if column_name not in summary_columns:
                    with engine.begin() as conn:
                        conn.execute(text(migration))
    except Exception:
        pass

def ensure_operation_rate_columns(engine):
    try:
        inspector = inspect(engine)
        if 'operation_rate' not in inspector.get_table_names():
            return
        columns = {column['name'] for column in inspector.get_columns('operation_rate')}
        if 'is_machine_operation' not in columns:
            with engine.begin() as conn:
                conn.execute(text(
                    'ALTER TABLE operation_rate '
                    'ADD COLUMN is_machine_operation BOOLEAN DEFAULT FALSE'
                ))
        if 'is_stitched_operation' not in columns:
            with engine.begin() as conn:
                conn.execute(text(
                    'ALTER TABLE operation_rate '
                    'ADD COLUMN is_stitched_operation BOOLEAN DEFAULT FALSE'
                ))
        if 'is_special_operation' not in columns:
            with engine.begin() as conn:
                conn.execute(text(
                    'ALTER TABLE operation_rate '
                    'ADD COLUMN is_special_operation BOOLEAN DEFAULT FALSE'
                ))
    except Exception:
        pass

def ensure_order_operation_rate_columns(engine):
    try:
        inspector = inspect(engine)
        if 'order_operation_rate' not in inspector.get_table_names():
            return
        columns = {column['name'] for column in inspector.get_columns('order_operation_rate')}
        if 'sort_order' not in columns:
            with engine.begin() as conn:
                conn.execute(text('ALTER TABLE order_operation_rate ADD COLUMN sort_order INTEGER DEFAULT 0'))
    except Exception:
        pass

def ensure_article_operation_rate_columns(engine):
    try:
        inspector = inspect(engine)
        if 'article_operation_rate' not in inspector.get_table_names():
            return
        columns = {column['name'] for column in inspector.get_columns('article_operation_rate')}
        if 'sort_order' not in columns:
            with engine.begin() as conn:
                conn.execute(text('ALTER TABLE article_operation_rate ADD COLUMN sort_order INTEGER DEFAULT 0'))
        if 'is_enabled' not in columns:
            with engine.begin() as conn:
                conn.execute(text('ALTER TABLE article_operation_rate ADD COLUMN is_enabled BOOLEAN NOT NULL DEFAULT TRUE'))
        if 'is_special_operation' not in columns:
            with engine.begin() as conn:
                conn.execute(text('ALTER TABLE article_operation_rate ADD COLUMN is_special_operation BOOLEAN NOT NULL DEFAULT FALSE'))
    except Exception:
        pass


def ensure_article_operation_rate_history_columns(engine):
    try:
        inspector = inspect(engine)
        if 'article_operation_rate_history' not in inspector.get_table_names():
            return
        columns = {column['name'] for column in inspector.get_columns('article_operation_rate_history')}
        if 'portal_name' not in columns:
            with engine.begin() as conn:
                conn.execute(text('ALTER TABLE article_operation_rate_history ADD COLUMN portal_name VARCHAR(150) NOT NULL DEFAULT \"\"'))
    except Exception:
        pass


def migrate_article_operation_rate_settings():
    try:
        legacy_special_rate_ids = {
            rate.id for rate in OperationRate.query.filter_by(is_special_operation=True).all()
        }
        assignments = ArticleOperationRate.query.all()
        for assignment in assignments:
            if assignment.rate_id in legacy_special_rate_ids:
                assignment.is_special_operation = True
                assignment.is_enabled = False

        if legacy_special_rate_ids:
            for selection in CutSpecialOperation.query.filter(
                CutSpecialOperation.rate_id.in_(legacy_special_rate_ids)
            ).all():
                order = Order.query.get(selection.order_id)
                article = get_article_for_order(order)
                if not article:
                    continue
                assignment = ArticleOperationRate.query.filter_by(
                    article_id=article.id,
                    rate_id=selection.rate_id,
                ).first()
                if not assignment:
                    db.session.add(ArticleOperationRate(
                        article_id=article.id,
                        rate_id=selection.rate_id,
                        is_enabled=False,
                        is_special_operation=True,
                    ))
                elif not assignment.is_special_operation:
                    assignment.is_special_operation = True
                    assignment.is_enabled = False

        history_keys = {
            (history.article_id, history.rate_id)
            for history in ArticleOperationRateHistory.query.all()
        }
        for assignment in ArticleOperationRate.query.all():
            history_key = (assignment.article_id, assignment.rate_id)
            if history_key not in history_keys:
                db.session.add(ArticleOperationRateHistory(
                    article_id=assignment.article_id,
                    rate_id=assignment.rate_id,
                    override_rate=assignment.override_rate,
                    effective_date=assignment.created_at or datetime.utcnow(),
                    portal_name='',
                ))
                history_keys.add(history_key)

        for rate in OperationRate.query.filter_by(is_special_operation=True).all():
            rate.is_special_operation = False
        db.session.commit()
    except Exception:
        db.session.rollback()


def ensure_article_schema(engine):
    try:
        inspector = inspect(engine)
        article_columns = {column['name'] for column in inspector.get_columns('article')}
        article_additions = {
            'finish_size': 'ALTER TABLE article ADD COLUMN finish_size VARCHAR(50) DEFAULT ""',
            'length': 'ALTER TABLE article ADD COLUMN length VARCHAR(50) DEFAULT ""',
            'width': 'ALTER TABLE article ADD COLUMN width VARCHAR(50) DEFAULT ""',
            'fabric_type': 'ALTER TABLE article ADD COLUMN fabric_type VARCHAR(100) DEFAULT ""',
        }
        with engine.begin() as conn:
            for column_name, sql in article_additions.items():
                if column_name not in article_columns:
                    try:
                        conn.execute(text(sql))
                    except Exception:
                        pass
    except Exception:
        pass


def ensure_vendor_schema(engine):
    try:
        inspector = inspect(engine)
        for table_name, table_columns in {
            'vendor': {
                'name': 'VARCHAR(150)',
                'code': 'VARCHAR(50)',
                'contact_person': 'VARCHAR(150)',
                'phone': 'VARCHAR(50)',
                'email': 'VARCHAR(150)',
                'address': 'VARCHAR(255)',
                'notes': 'TEXT',
                'created_at': 'DATETIME',
            },
            'vendor_item': {
                'vendor_id': 'INTEGER',
                'item_name': 'VARCHAR(150)',
                'material': 'VARCHAR(150)',
                'size': 'VARCHAR(50)',
                'unit': 'VARCHAR(50)',
                'pack_qty': 'FLOAT',
                'pack_price': 'FLOAT',
                'rate': 'FLOAT',
                'notes': 'TEXT',
                'created_at': 'DATETIME',
            },
            'saved_requirement': {
                'roll_length_m': 'FLOAT NOT NULL DEFAULT 0',
            },
            'item_master': {
                'item_name': 'VARCHAR(150)',
                'material': 'VARCHAR(150)',
                'size': 'VARCHAR(50)',
                'unit': 'VARCHAR(50)',
                'returnable': 'BOOLEAN NOT NULL DEFAULT FALSE',
                'created_at': 'DATETIME',
            },
            'article_material_spec': {
                'article_id': 'INTEGER',
                'item_name': 'VARCHAR(150)',
                'material': 'VARCHAR(150)',
                'size': 'VARCHAR(50)',
                'qty_per_piece': 'VARCHAR(50)',
                'unit': 'VARCHAR(50)',
                'item_type': 'VARCHAR(50)',
                'sort_order': 'INTEGER',
                'created_at': 'DATETIME',
            },
        }.items():
            if table_name not in inspector.get_table_names():
                continue
            existing_columns = {column['name'] for column in inspector.get_columns(table_name)}
            with engine.begin() as conn:
                for column_name, column_type in table_columns.items():
                    if column_name not in existing_columns:
                        try:
                            conn.execute(text(f'ALTER TABLE {table_name} ADD COLUMN {column_name} {column_type}'))
                        except Exception:
                            pass
    except Exception:
        pass

# Initialize Tables
with app.app_context():
    print("Creating tables...")
    db.create_all()
    for table_name in ('billing_invoice_line', 'customer_bill_line'):
        columns = {
            column['name'] for column in inspect(db.engine).get_columns(table_name)
        }
        if 'challan_id' not in columns:
            with db.engine.begin() as conn:
                conn.execute(text(
                    f'ALTER TABLE {table_name} ADD COLUMN challan_id INTEGER'
                ))
    for invoice in BillingInvoice.query.all():
        if not BillingInvoiceChallan.query.filter_by(
            invoice_id=invoice.id,
            challan_id=invoice.challan_id,
        ).first():
            db.session.add(BillingInvoiceChallan(
                invoice_id=invoice.id,
                challan_id=invoice.challan_id,
            ))
        for line in invoice.lines:
            if line.challan_id is None:
                line.challan_id = invoice.challan_id
    for bill in CustomerBill.query.all():
        if not CustomerBillChallan.query.filter_by(
            bill_id=bill.id,
            challan_id=bill.challan_id,
        ).first():
            db.session.add(CustomerBillChallan(
                bill_id=bill.id,
                challan_id=bill.challan_id,
            ))
        for line in bill.lines:
            if line.challan_id is None:
                line.challan_id = bill.challan_id
    db.session.commit()
    supplier_return_columns = {
        column['name']
        for column in inspect(db.engine).get_columns('accessory_supplier_return')
    }
    with db.engine.begin() as conn:
        if 'exchange_item' not in supplier_return_columns:
            conn.execute(text(
                'ALTER TABLE accessory_supplier_return ADD COLUMN exchange_item VARCHAR(150) DEFAULT \'\''
            ))
        if 'exchange_item_unit' not in supplier_return_columns:
            conn.execute(text(
                'ALTER TABLE accessory_supplier_return ADD COLUMN exchange_item_unit VARCHAR(50) DEFAULT \'\''
            ))
    for table_name in ('inventory', 'saved_requirement'):
        table_columns = {
            column['name'] for column in inspect(db.engine).get_columns(table_name)
        }
        if 'created_at' not in table_columns:
            with db.engine.begin() as conn:
                conn.execute(text(
                    f'ALTER TABLE {table_name} ADD COLUMN created_at TIMESTAMP'
                ))
    issue_columns = {
        column['name'] for column in inspect(db.engine).get_columns('accessory_issue')
    }
    if 'storage_location_id' not in issue_columns:
        with db.engine.begin() as conn:
            conn.execute(text(
                'ALTER TABLE accessory_issue ADD COLUMN storage_location_id '
                'INTEGER REFERENCES accessory_storage_location(id) ON DELETE SET NULL'
            ))
    storage_columns = {
        column['name']
        for column in inspect(db.engine).get_columns('accessory_storage_location')
    }
    if 'description' not in storage_columns:
        with db.engine.begin() as conn:
            conn.execute(text(
                'ALTER TABLE accessory_storage_location ADD COLUMN description VARCHAR(200) DEFAULT \'\''
            ))
    if 'department' not in storage_columns:
        with db.engine.begin() as conn:
            conn.execute(text(
                'ALTER TABLE accessory_storage_location ADD COLUMN department VARCHAR(100) NOT NULL DEFAULT \'\''
            ))
    if 'gala' not in storage_columns:
        with db.engine.begin() as conn:
            conn.execute(text(
                'ALTER TABLE accessory_storage_location ADD COLUMN gala VARCHAR(100) NOT NULL DEFAULT \'\''
            ))
    for location in AccessoryStorageLocation.query.filter(
        AccessoryStorageLocation.department.isnot(None),
        AccessoryStorageLocation.department != '',
        AccessoryStorageLocation.room.isnot(None),
        AccessoryStorageLocation.room != '',
    ).all():
        department = Department.query.filter(
            func.lower(func.trim(Department.name)) == location.department.strip().casefold()
        ).first()
        if department and not DepartmentStoreRoom.query.filter(
            DepartmentStoreRoom.department_id == department.id,
            func.lower(func.trim(DepartmentStoreRoom.name)) == location.room.strip().casefold(),
        ).first():
            db.session.add(DepartmentStoreRoom(
                department_id=department.id,
                name=location.room.strip(),
            ))
    db.session.commit()
    ensure_portal_account_access_column(db.engine)
    ensure_portal_account_page_access_column(db.engine)
    ensure_item_master_issue_columns(db.engine)
    seed_portal_accounts()
    ensure_table_columns(db.engine)
    ensure_operation_rate_columns(db.engine)
    ensure_order_operation_rate_columns(db.engine)
    ensure_article_operation_rate_columns(db.engine)
    ensure_article_operation_rate_history_columns(db.engine)
    migrate_article_operation_rate_settings()
    ensure_article_schema(db.engine)
    ensure_vendor_schema(db.engine)
    try:
        inspector = inspect(db.engine)
        if 'attendance' in inspector.get_table_names():
            attendance_columns = [column['name'] for column in inspector.get_columns('attendance')]
            if 'night_hours' not in attendance_columns:
                try:
                    with db.engine.begin() as conn:
                        conn.execute(text('ALTER TABLE attendance ADD COLUMN night_hours FLOAT DEFAULT 0'))
                except Exception:
                    pass
            for attendance_column in ('late_days', 'on_time_days'):
                if attendance_column not in attendance_columns:
                    try:
                        with db.engine.begin() as conn:
                            conn.execute(text(f'ALTER TABLE attendance ADD COLUMN {attendance_column} INTEGER DEFAULT 0'))
                    except Exception:
                        pass
        if 'operation_rate_history' in inspector.get_table_names():
            history_columns = [c['name'] for c in inspector.get_columns('operation_rate_history')]
            if 'order_id' not in history_columns:
                with db.engine.begin() as conn:
                    conn.execute(text('ALTER TABLE operation_rate_history ADD COLUMN order_id INTEGER'))
    except Exception:
        pass

    print("Updating PostgreSQL schema...")
    update_postgres_schema()
    print("Updating Inventory schema...")
    update_inventory_schema()
    print("Updating shipment and challan schema...")
    update_shipment_challan_schema()
    print("Updating Order schema...")
    update_order_schema()
    print("Updating Article schema...")
    update_article_schema()
    print("Updating Worker schema...")
    update_worker_schema()
    print("Updating Payment schema...")
    update_payment_schema()
    print("Updating Receiving Challan schema...")
    update_receiving_challan_schema()

    try:
        inspector = inspect(db.engine)
        if 'article_operation_rate' in inspector.get_table_names():
            existing_aor = [c['name'] for c in inspector.get_columns('article_operation_rate')]
            if 'override_rate' not in existing_aor:
                with db.engine.begin() as conn:
                    conn.execute(text('ALTER TABLE article_operation_rate ADD COLUMN override_rate FLOAT'))
    except Exception:
        pass

    # Add order costing metadata to existing accessory issue records.
    try:
        inspector = inspect(db.engine)
        if 'accessory_issue' in inspector.get_table_names():
            existing_issue_columns = {column['name'] for column in inspector.get_columns('accessory_issue')}
            with db.engine.begin() as conn:
                if 'order_id' not in existing_issue_columns:
                    conn.execute(text('ALTER TABLE accessory_issue ADD COLUMN order_id VARCHAR(100)'))
                if 'unit_rate' not in existing_issue_columns:
                    conn.execute(text('ALTER TABLE accessory_issue ADD COLUMN unit_rate FLOAT NOT NULL DEFAULT 0'))
    except Exception:
        pass

    inspector = inspect(db.engine)
    if 'accessory_issue' in inspector.get_table_names():
        existing_issue_columns = {
            column['name'] for column in inspector.get_columns('accessory_issue')
        }
        with db.engine.begin() as conn:
            if 'cut_no' not in existing_issue_columns:
                conn.execute(text('ALTER TABLE accessory_issue ADD COLUMN cut_no VARCHAR(50)'))
            if 'cut_sheet_id' not in existing_issue_columns:
                conn.execute(text(
                    'ALTER TABLE accessory_issue ADD COLUMN cut_sheet_id INTEGER '
                    'REFERENCES cutting_sheet(id) ON DELETE SET NULL'
                ))
            if 'cutting_pcs' not in existing_issue_columns:
                conn.execute(text('ALTER TABLE accessory_issue ADD COLUMN cutting_pcs FLOAT'))
            if 'issued_as_qty' not in existing_issue_columns:
                conn.execute(text('ALTER TABLE accessory_issue ADD COLUMN issued_as_qty FLOAT NOT NULL DEFAULT 0'))
            if 'issued_as_unit' not in existing_issue_columns:
                conn.execute(text("ALTER TABLE accessory_issue ADD COLUMN issued_as_unit VARCHAR(50) DEFAULT ''"))
            if 'issue_conversion_factor' not in existing_issue_columns:
                conn.execute(text('ALTER TABLE accessory_issue ADD COLUMN issue_conversion_factor FLOAT NOT NULL DEFAULT 1'))

    # Ensure SavedRequirement has new columns (run after create_all so table exists)
    try:
        inspector = inspect(db.engine)
        if 'saved_requirement' in inspector.get_table_names():
            existing = [c['name'] for c in inspector.get_columns('saved_requirement')]
            conn = db.engine.connect()
            try:
                if 'rate' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN rate VARCHAR(100)'))
                if 'bill_amount' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN bill_amount VARCHAR(100)'))
                if 'supplier' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN supplier VARCHAR(200)'))
                if 'unit' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN unit VARCHAR(50)'))
                if 'issue_unit' not in existing:
                    conn.execute(text("ALTER TABLE saved_requirement ADD COLUMN issue_unit VARCHAR(50) DEFAULT ''"))
                if 'issue_unit_factor' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN issue_unit_factor FLOAT NOT NULL DEFAULT 1'))
                if 'accessory_status' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN accessory_status VARCHAR(30)'))
                if 'received_qty' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN received_qty VARCHAR(50)'))
                if 'issued_qty' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN issued_qty VARCHAR(50)'))
                if 'used_qty' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN used_qty VARCHAR(50)'))
                if 'po_sent_at' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN po_sent_at VARCHAR(50)'))
                if 'purchase_slip_image' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN purchase_slip_image VARCHAR(255)'))
                if 'received_at' not in existing:
                    conn.execute(text('ALTER TABLE saved_requirement ADD COLUMN received_at VARCHAR(50)'))
            except Exception:
                pass
            finally:
                conn.close()
            # Ensure CuttingSheet has fabric_meter/total_meter columns for older DBs
            try:
                if 'cutting_sheet' in inspector.get_table_names():
                    existing_cs = [c['name'] for c in inspector.get_columns('cutting_sheet')]
                    conn2 = db.engine.connect()
                    try:
                        if 'cut_no' not in existing_cs:
                            conn2.execute(text('ALTER TABLE cutting_sheet ADD COLUMN cut_no VARCHAR(50)'))
                        if 'fabric_meter' not in existing_cs:
                            conn2.execute(text('ALTER TABLE cutting_sheet ADD COLUMN fabric_meter VARCHAR(100)'))
                        if 'total_meter' not in existing_cs:
                            conn2.execute(text('ALTER TABLE cutting_sheet ADD COLUMN total_meter VARCHAR(100)'))
                        if 'total_palla' not in existing_cs:
                            conn2.execute(text('ALTER TABLE cutting_sheet ADD COLUMN total_palla VARCHAR(100)'))
                        if 'total_pcs' not in existing_cs:
                            conn2.execute(text('ALTER TABLE cutting_sheet ADD COLUMN total_pcs VARCHAR(100)'))
                        if 'shortage' not in existing_cs:
                            conn2.execute(text('ALTER TABLE cutting_sheet ADD COLUMN shortage VARCHAR(50)'))
                        if 'cut_date' not in existing_cs:
                            conn2.execute(text('ALTER TABLE cutting_sheet ADD COLUMN cut_date VARCHAR(100)'))
                    except Exception:
                        pass
                    finally:
                        conn2.close()
            except Exception:
                pass

            # Ensure OperationRateHistory has effective_date column (older DBs may miss it)
            try:
                if 'operation_rate_history' in inspector.get_table_names():
                    existing_or = [c['name'] for c in inspector.get_columns('operation_rate_history')]
                    conn3 = db.engine.connect()
                    try:
                        if 'effective_date' not in existing_or:
                            try:
                                conn3.execute(text('ALTER TABLE operation_rate_history ADD COLUMN effective_date DATETIME'))
                            except Exception:
                                pass
                    finally:
                        conn3.close()
            except Exception:
                pass

        # Seed OperationRate table with sensible defaults if empty
        try:
            if 'operation_rate' in inspector.get_table_names():
                if OperationRate.query.count() == 0:
                    default_ops = {
                        "FOLDING": 0.40,
                        "PACKING": 0.50,
                        "STITCHING": 1.20,
                        "CHECKING": 0.30
                    }
                    for op, r in default_ops.items():
                        try:
                            db.session.add(OperationRate(operation=op, rate=float(r)))
                        except Exception:
                            pass
                    db.session.commit()
        except Exception:
            db.session.rollback()
            pass
    except Exception:
        pass

def redirect_after_portal_login(default_endpoint):
    next_url = (request.values.get('next') or '').strip()
    parsed_url = urlparse(next_url)
    if (
        next_url
        and parsed_url.scheme == ''
        and parsed_url.netloc == ''
        and parsed_url.path.startswith('/')
        and not parsed_url.path.startswith('//')
        and '\\' not in next_url
    ):
        return redirect(next_url)
    return redirect(url_for(default_endpoint))


@app.route('/')
def index():
    if 'user' in session:
        if session.get('role') == 'owner':
            return redirect(url_for('owner_dashboard'))
        account = PortalAccount.query.filter_by(username=session.get('user')).first()
        available_portals = account_portals(account) if account else set()
        primary_portal = session.get('profile_role', session.get('role'))
        primary_endpoint = {
            'stock': 'stock_portal',
            'accounts': 'accounts_portal',
            'challan': 'challan_portal',
        }.get(primary_portal)
        if primary_endpoint and primary_portal in available_portals:
            return redirect(url_for(primary_endpoint))
        if 'manager' in available_portals or 'operations' in available_portals or 'assistant_manager' in available_portals:
            return redirect(url_for('manager_dashboard'))
        for portal, endpoint in (('stock', 'stock_portal'), ('accounts', 'accounts_portal'), ('challan', 'challan_portal')):
            if portal in available_portals:
                return redirect(url_for(endpoint))
    return render_template('dashboard.html', welcome=True)

@app.route('/login/<target_role>', methods=['GET', 'POST'])
def login(target_role):
    if request.method == 'POST':
        username = request.form.get('username', '').strip().lower()
        password = request.form.get('password', '')
        
        # Check owner-managed portal accounts.
        portal_account = PortalAccount.query.filter_by(username=username).first()
        if portal_account and portal_account.password == password:
            account_role = portal_account.role
            if target_role in ALL_PORTALS:
                if account_role == 'owner' or target_role in account_portals(portal_account):
                    session_role = 'manager' if account_role == 'operations_manager' else account_role
                    session.update({'user': username, 'role': session_role, 'profile_role': account_role, 'name': portal_account.name})
                    default_endpoint = {
                        'manager': 'manager_dashboard',
                        'operations': 'manager_dashboard',
                        'assistant_manager': 'manager_dashboard',
                        'accounts': 'accounts_portal',
                        'stock': 'stock_portal',
                        'challan': 'challan_portal',
                    }[target_role]
                    return redirect_after_portal_login(default_endpoint)
                flash('This profile does not have access to the selected portal.', 'danger')
                return render_template('login.html', role=target_role)
            if target_role != account_role:
                flash('Please use the correct portal for this account.', 'danger')
                return render_template('login.html', role=target_role)
            session.update({
                'user': username, 
                'role': account_role, 
                'name': portal_account.name
            })
            if account_role == 'owner':
                return redirect_after_portal_login('owner_dashboard')
            return redirect_after_portal_login('manager_dashboard')
        
        # Check worker accounts using the assigned Worker ID and CNIC.
        worker = Worker.query.filter(func.lower(Worker.worker_code) == username).first()
        if worker and worker.cnic and worker.cnic.strip() == password.strip():
            if target_role != 'worker':
                flash('Please use the Worker portal for this account.', 'danger')
                return render_template('login.html', role=target_role)
            session.update({
                'user': worker.worker_code,
                'role': 'worker',
                'name': worker.name or f"Worker: {worker.worker_code}",
                'worker_name': worker.name,
                'worker_id': worker.id,
            })
            return redirect(url_for('worker_dashboard'))
            
        flash("Invalid Credentials!", "danger")
        
    return render_template('login.html', role=target_role)


@app.route('/accounts')
def accounts_portal():
    if session.get('role') not in ('owner', 'manager', 'accounts'):
        return redirect(url_for('login', target_role='accounts', next=url_for('accounts_portal')))
    return render_template('accounts.html')


def accounts_management_access(default_role='accounts'):
    if session.get('role') in ('owner', 'manager', 'accounts'):
        return None
    return redirect(url_for('login', target_role=default_role, next=request.full_path))


@app.route('/accounts/credit-debit-ledger', methods=['GET', 'POST'])
def accounts_credit_debit_ledger():
    return render_credit_debit_ledger()


@app.route('/accounts/company-credit-debit', methods=['GET', 'POST'])
def accounts_company_credit_debit():
    return render_credit_debit_ledger(company_mode=True)


def render_credit_debit_ledger(company_mode=False):
    denied = accounts_management_access('accounts')
    if denied:
        return denied

    company = (request.values.get('company') or request.args.get('company') or 'Canon').strip().title()
    if company not in ('Canon', 'Haram'):
        company = 'Canon'
    selected_party = (request.values.get('party') or request.args.get('party') or '').strip()

    if request.method == 'POST':
        direction_value = (request.form.get('manual_direction') or '').strip().upper()
        description_value = (request.form.get('manual_description') or '').strip()
        date_value = (request.form.get('manual_date') or '').strip()
        manual_company = (request.form.get('manual_company') or company).strip().title()
        parsed_date = normalize_date(date_value)
        try:
            amount_value = parse_billing_amount(request.form.get('manual_amount'), 'Amount')
        except ValueError as exc:
            flash(str(exc), 'danger')
            return redirect(url_for(
                'accounts_company_credit_debit' if company_mode else 'accounts_credit_debit_ledger',
                q=request.form.get('q', ''),
                direction=request.form.get('direction', 'ALL'),
                start_date=request.form.get('start_date', ''),
                end_date=request.form.get('end_date', ''),
                company=company if company_mode else None,
                party=request.form.get('party', ''),
            ))
        if direction_value not in ('CREDIT', 'DEBIT'):
            flash('Choose whether this entry is a credit or debit.', 'danger')
        elif manual_company not in ('Canon', 'Haram'):
            flash('Choose Canon or Haram for this entry.', 'danger')
        elif not parsed_date:
            flash('Enter a valid transaction date.', 'danger')
        elif not description_value:
            flash('Enter a transaction description.', 'danger')
        elif amount_value <= 0:
            flash('Amount must be greater than zero.', 'danger')
        else:
            db.session.add(ManualCreditDebitEntry(
                date=parsed_date.strftime('%Y-%m-%d'),
                direction=direction_value,
                description=description_value,
                reference=(request.form.get('manual_reference') or '').strip(),
                method=(request.form.get('manual_method') or 'Manual').strip() or 'Manual',
                amount=amount_value,
                party_name=(request.form.get('manual_party') or '').strip(),
                company=manual_company,
                created_by=session.get('name') or session.get('user') or '',
            ))
            db.session.commit()
            flash('Manual credit/debit entry recorded.', 'success')
        return redirect(url_for(
            'accounts_company_credit_debit' if company_mode else 'accounts_credit_debit_ledger',
            q=request.form.get('q', ''),
            direction=request.form.get('direction', 'ALL'),
            start_date=request.form.get('start_date', ''),
            end_date=request.form.get('end_date', ''),
            company=company if company_mode else None,
            party=request.form.get('party', ''),
        ))

    entries = []
    mirrored_payment_counts = {}
    customer_bills = CustomerBill.query.order_by(CustomerBill.id.asc()).all()
    bills_by_challan = {bill.challan_id: bill for bill in customer_bills}

    def payment_signature(challan_id, payment):
        return (
            challan_id,
            payment.paid_on or '',
            round(parse_numeric(payment.amount), 2),
            (payment.method or '').casefold(),
            (payment.reference or '').strip().casefold(),
        )

    def add_entry(
        date_value, direction, category, description, reference, method, amount,
        exchange_sort_id=0, exchange_sort_order=0, recorded_at=None,
        company='Canon', party='',
    ):
        amount = round(parse_numeric(amount), 2)
        if amount <= 0:
            return
        if isinstance(date_value, datetime):
            date_value = date_value.strftime('%Y-%m-%d')
        date_text = str(date_value or '').strip()
        parsed_date = normalize_date(date_text)
        entries.append({
            'sort_date': parsed_date or datetime.min,
            'sort_recorded_at': ledger_recorded_at(recorded_at, date_value),
            'exchange_sort_id': exchange_sort_id,
            'exchange_sort_order': exchange_sort_order,
            'date': parsed_date.strftime('%d/%m/%Y') if parsed_date else (date_text or 'â€”'),
            'direction': direction,
            'category': category,
            'description': description or category,
            'reference': reference or 'â€”',
            'method': method or 'â€”',
            'company': normalize_challan_shipper(company),
            'party': (party or '').strip(),
            'credit_amount': amount if direction == 'CREDIT' else 0.0,
            'debit_amount': amount if direction == 'DEBIT' else 0.0,
        })

    for bill in customer_bills:
        for payment in bill.payments:
            signature = payment_signature(bill.challan_id, payment)
            mirrored_payment_counts[signature] = mirrored_payment_counts.get(signature, 0) + 1
            add_entry(
                payment.paid_on,
                'CREDIT',
                'Customer receipt',
                bill.party_name,
                bill.bill_no,
                payment.method,
                payment.amount,
                recorded_at=payment.created_at,
                company=bill.challan.shipped_by_party if bill.challan else 'Canon',
                party=bill.party_name,
            )

    for invoice in BillingInvoice.query.order_by(BillingInvoice.id.asc()).all():
        for payment in invoice.payments:
            signature = payment_signature(invoice.challan_id, payment)
            if mirrored_payment_counts.get(signature, 0):
                mirrored_payment_counts[signature] -= 1
                continue
            add_entry(
                payment.paid_on,
                'CREDIT',
                'Customer receipt',
                invoice.party_name,
                invoice.invoice_no,
                payment.method,
                payment.amount,
                recorded_at=payment.created_at,
                company=invoice.challan.shipped_by_party if invoice.challan else 'Canon',
                party=invoice.party_name,
            )

    accessory_purchases = SavedRequirement.query.order_by(
        SavedRequirement.id.asc()
    ).all()

    def company_for_order(job_no):
        order = Order.query.filter_by(job_no=job_no).first() if job_no else None
        if not order:
            return 'Canon'
        shipment = ShipmentRecord.query.filter_by(order_id=order.id).order_by(
            ShipmentRecord.id.desc()
        ).first()
        if shipment:
            return normalize_challan_shipper(shipment.shipped_by_party)
        challan = ChallanRecord.query.filter_by(
            order_id=order.id, source_type='order'
        ).order_by(ChallanRecord.id.desc()).first()
        return normalize_challan_shipper(challan.shipped_by_party if challan else 'Canon')

    for requirement in accessory_purchases:
        if accessory_layer_received_qty(requirement) <= 0:
            continue
        purchase_amount = parse_numeric(requirement.bill_amount)
        purchase_method = 'Accessory bill'
        if purchase_amount <= 0:
            purchase_amount = (
                parse_numeric(requirement.qty) * parse_numeric(requirement.rate)
            )
            purchase_method = 'PO quantity × rate'
        add_entry(
            requirement.date,
            'CREDIT',
            'Accessory purchase',
            ' · '.join(value for value in (requirement.supplier, requirement.item) if value),
            f'PO {requirement.po_no}' if requirement.po_no else f'Requirement #{requirement.id}',
            purchase_method,
            purchase_amount,
            recorded_at=requirement.created_at,
            company=company_for_order(requirement.order_id),
            party=requirement.supplier,
        )

    for supplier_return in AccessorySupplierReturn.query.order_by(
        AccessorySupplierReturn.id.asc()
    ).all():
        requirement = supplier_return.requirement
        if not requirement:
            continue
        return_value = (
            parse_numeric(supplier_return.returned_qty)
            * parse_numeric(supplier_return.unit_rate)
        )
        return_type = (supplier_return.return_type or 'RETURN').strip().upper()
        return_description = ' · '.join(
            value for value in (
                requirement.supplier,
                requirement.item,
                supplier_return.note,
            ) if value
        )
        debit_description = (
            f'{return_description} · EXCHANGE ITEM RECEIVED'
            if return_type == 'EXCHANGE' else return_description
        )
        if return_type == 'EXCHANGE':
            return_reference = (
                f'PO {requirement.po_no} . EXCHANGE #{supplier_return.id}'
                if requirement.po_no else f'Requirement #{requirement.id} . EXCHANGE #{supplier_return.id}'
            )
        else:
            return_reference = (
                f'PO {requirement.po_no} · Return #{supplier_return.id}'
                if requirement.po_no else f'Requirement #{requirement.id} · Return #{supplier_return.id}'
            )
        add_entry(
            supplier_return.return_date,
            'DEBIT',
            f'Accessory supplier {return_type.lower()}',
            debit_description,
            return_reference,
            f'Supplier {return_type.lower()}',
            return_value,
            supplier_return.id if return_type == 'EXCHANGE' else 0,
            1 if return_type == 'EXCHANGE' else 0,
            supplier_return.created_at,
            company=company_for_order(requirement.order_id),
            party=requirement.supplier,
        )
        if return_type == 'EXCHANGE':
            add_entry(
                supplier_return.return_date,
                'CREDIT',
                'Accessory supplier exchange credit',
                ' · '.join(value for value in (
                    return_description,
                    f'Replacement: {supplier_return.exchange_item}'
                    if supplier_return.exchange_item else '',
                    'EXCHANGE ACCEPTED',
                ) if value),
                return_reference,
                'Supplier exchange',
                return_value,
                supplier_return.id,
                0,
                supplier_return.created_at,
            )

    utility_payments = UtilityBillPayment.query.order_by(UtilityBillPayment.id.asc()).all() if company_mode else []
    for payment in utility_payments:
        bill = payment.bill
        if bill:
            add_entry(
                payment.paid_on,
                'DEBIT',
                'Utility payment',
                f'{bill.utility_type} · {bill.provider}',
                bill.account_reference or f'Bill #{bill.id}',
                payment.method,
                payment.amount,
                recorded_at=payment.created_at,
                company=bill.company,
                party=bill.provider,
            )

    workers_by_id = {worker.id: worker for worker in Worker.query.all()}
    salary_payments = SalaryPayment.query.order_by(SalaryPayment.id.asc()).all() if company_mode else []
    for payment in salary_payments:
        worker = workers_by_id.get(payment.worker_id)
        payment_amount = parse_numeric(payment.amount)
        if payment_amount <= 0 and worker:
            payment_amount = calculate_payroll_payment_amount(
                worker,
                payment.payout_portal,
                payment.period_start,
                payment.period_end,
                exclude_payment_id=payment.id,
            )
        if payment_amount > 0:
            add_entry(
                payment.paid_at,
                'DEBIT',
                'Salary payout',
                payment.period_label or payment.period_type or 'Payroll',
                payment.period_type or 'Payroll',
                payment.payout_portal,
                payment_amount,
                recorded_at=payment.paid_at,
                company=payment.company,
                party=worker.name if worker else 'Worker',
            )

    for manual_entry in ManualCreditDebitEntry.query.order_by(ManualCreditDebitEntry.id.asc()).all():
        if not company_mode and (manual_entry.reference or '').upper().startswith('PETTY-CASH-'):
            continue
        add_entry(
            manual_entry.date,
            manual_entry.direction,
            'Petty cash' if (manual_entry.reference or '').startswith('PETTY-CASH-') else 'Manual entry',
            manual_entry.description,
            manual_entry.reference,
            manual_entry.method,
            manual_entry.amount,
            recorded_at=manual_entry.created_at,
            company=manual_entry.company,
            party=manual_entry.party_name or manual_entry.description,
        )

    search = (request.args.get('q') or '').strip().casefold()
    direction = (request.args.get('direction') or 'ALL').upper()
    if direction not in ('ALL', 'CREDIT', 'DEBIT'):
        direction = 'ALL'
    start_text = (request.args.get('start_date') or '').strip()
    end_text = (request.args.get('end_date') or '').strip()
    start_date = normalize_date(start_text)
    end_date = normalize_date(end_text)
    if company_mode:
        selected_party = ''
    party_names = sorted({
        party_name.strip()
        for (party_name,) in db.session.query(Article.party_name)
        .filter(Article.party_name.isnot(None), Article.party_name != '')
        .distinct()
        .all()
        if party_name and party_name.strip()
    }, key=str.casefold)
    visible_entries = [
        entry for entry in entries
        if (not company_mode or entry['company'] == company)
        if (not selected_party or entry['party'].casefold() == selected_party.casefold())
        if (direction == 'ALL' or entry['direction'] == direction)
        and (not start_date or entry['sort_date'] >= start_date)
        and (not end_date or entry['sort_date'] <= end_date.replace(hour=23, minute=59, second=59))
    ]
    visible_entries.sort(
        key=lambda entry: (
            entry['sort_recorded_at'],
            entry['exchange_sort_id'],
            entry['exchange_sort_order'],
        ),
        reverse=True,
    )
    total_credit = round(sum(entry['credit_amount'] for entry in visible_entries), 2)
    total_debit = round(sum(entry['debit_amount'] for entry in visible_entries), 2)
    statement_entries = []
    statement_opening_balance = 0.0
    statement_carried_forward_balance = 0.0
    statement_scope_entries = [
        entry for entry in entries
        if (not company_mode or entry['company'] == company)
        if (not selected_party or entry['party'].casefold() == selected_party.casefold())
    ]
    chronological_entries = sorted(
        statement_scope_entries,
        key=lambda entry: (
            entry['sort_date'],
            entry['sort_recorded_at'],
            entry['exchange_sort_id'],
            entry['exchange_sort_order'],
        ),
    )
    running_balance = 0.0
    for entry in chronological_entries:
        change = entry['credit_amount'] - entry['debit_amount']
        running_balance += change
        entry['running_balance'] = round(running_balance, 2)
        if start_date and entry['sort_date'] < start_date:
            statement_opening_balance += change
        if not end_date or entry['sort_date'] <= end_date.replace(
            hour=23, minute=59, second=59
        ):
            statement_carried_forward_balance += change
    statement_entries = sorted(
        visible_entries,
        key=lambda entry: (
            entry['sort_date'],
            entry['sort_recorded_at'],
            entry['exchange_sort_id'],
            entry['exchange_sort_order'],
        ),
    )
    statement_opening_balance = round(statement_opening_balance, 2)
    statement_carried_forward_balance = round(
        statement_carried_forward_balance, 2
    )

    return render_template(
        'credit_debit_ledger.html',
        company_mode=company_mode,
        company=company,
        party_names=party_names,
        selected_party=selected_party,
        entries=visible_entries,
        statement_entries=statement_entries,
        statement_opening_balance=statement_opening_balance,
        statement_carried_forward_balance=statement_carried_forward_balance,
        total_credit=total_credit,
        total_debit=total_debit,
        net_balance=round(total_credit - total_debit, 2),
        search=request.args.get('q', ''),
        direction=direction,
        start_date=start_text,
        end_date=end_text,
        today=datetime.utcnow().strftime('%Y-%m-%d'),
        printed_on=datetime.utcnow().strftime('%d/%m/%Y'),
        statement_period_start=start_date.strftime('%d/%m/%Y') if start_date else '',
        statement_period_end=end_date.strftime('%d/%m/%Y') if end_date else '',
    )


def settle_petty_cash_months(current_month, closed_at=None):
    closed_at = closed_at or datetime.utcnow()
    previous_months = db.session.query(
        PettyCashEntry.month_key, PettyCashEntry.company
    ).filter(
        PettyCashEntry.month_key < current_month
    ).distinct().order_by(
        PettyCashEntry.month_key, PettyCashEntry.company
    ).all()

    for month_key, company in previous_months:
        if PettyCashMonthClose.query.filter_by(
            month_key=month_key, company=company
        ).first():
            continue
        year, month = (int(part) for part in month_key.split('-'))
        month_end_date = f"{month_key}-{calendar.monthrange(year, month)[1]:02d}"

        month_entries = PettyCashEntry.query.filter_by(
            month_key=month_key, company=company
        ).all()
        balance = round(sum(
            entry.amount if entry.transaction_type == 'ALLOCATION'
            else -entry.amount if entry.transaction_type == 'EXPENSE'
            else 0
            for entry in month_entries
        ), 2)
        returned_amount = max(balance, 0.0)
        close = PettyCashMonthClose(
            month_key=month_key,
            company=company,
            returned_amount=returned_amount,
            closed_at=closed_at,
        )
        db.session.add(close)

        if returned_amount > 0:
            ledger_entry = ManualCreditDebitEntry(
                date=month_end_date,
                direction='CREDIT',
                description=f'Petty cash balance returned for {month_key}',
                reference=f'PETTY-CASH-CLOSE-{month_key}-{company.upper()}',
                method='Petty cash return',
                amount=returned_amount,
                party_name='Petty Cash',
                company=company,
                created_by='System',
            )
            db.session.add(ledger_entry)
            db.session.flush()
            close.company_ledger_entry_id = ledger_entry.id

        db.session.add(PettyCashEntry(
            date=month_end_date,
            month_key=month_key,
            transaction_type='RETURN',
            company=company,
            description=f'Month-end balance returned to {company}',
            amount=returned_amount,
            created_by='System',
            created_at=closed_at,
        ))
        try:
            db.session.commit()
        except IntegrityError:
            db.session.rollback()
            if not PettyCashMonthClose.query.filter_by(
                month_key=month_key, company=company
            ).first():
                raise


@app.route('/accounts/petty-cash', methods=['GET', 'POST'])
def accounts_petty_cash():
    denied = accounts_management_access('accounts')
    if denied:
        return denied

    now = datetime.utcnow()
    current_month = now.strftime('%Y-%m')
    settle_petty_cash_months(current_month, now)

    if request.method == 'POST':
        transaction_type = (request.form.get('transaction_type') or '').strip().upper()
        company = (request.form.get('company') or '').strip().title()
        description = (request.form.get('description') or '').strip()
        date_value = (request.form.get('date') or '').strip()
        try:
            amount = parse_billing_amount(request.form.get('amount'), 'Amount')
            parsed_date = normalize_date(date_value)
            if transaction_type not in ('ALLOCATION', 'EXPENSE'):
                raise ValueError('Choose an allocation or expense entry.')
            if company not in ('Canon', 'Haram'):
                raise ValueError('Choose Canon or Haram as the funding company.')
            if not parsed_date or parsed_date.strftime('%Y-%m') != current_month:
                raise ValueError('Petty cash entries must be dated within the current month.')
            if parsed_date.date() > now.date():
                raise ValueError('Petty cash entries cannot be dated in the future.')
            if not description:
                raise ValueError('Description is required.')
            if amount <= 0:
                raise ValueError('Amount must be greater than zero.')

            month_entries = PettyCashEntry.query.filter_by(
                month_key=current_month, company=company
            ).all()
            balance = round(sum(
                entry.amount if entry.transaction_type == 'ALLOCATION'
                else -entry.amount if entry.transaction_type == 'EXPENSE'
                else 0
                for entry in month_entries
            ), 2)
            if transaction_type == 'EXPENSE' and amount > balance:
                raise ValueError(
                    f'Expense exceeds the {company} petty cash balance of PKR {balance:,.2f}.'
                )

            entry_date = parsed_date.strftime('%Y-%m-%d')
            entry = PettyCashEntry(
                date=entry_date,
                month_key=current_month,
                transaction_type=transaction_type,
                company=company,
                description=description,
                amount=amount,
                created_by=session.get('name') or session.get('user') or '',
            )
            db.session.add(entry)
            db.session.flush()

            if transaction_type == 'ALLOCATION':
                db.session.add(ManualCreditDebitEntry(
                    date=entry_date,
                    direction='DEBIT',
                    description=f'Petty cash allocation: {description}',
                    reference=f'PETTY-CASH-{entry.id}',
                    method='Petty cash transfer',
                    amount=amount,
                    party_name='Petty Cash',
                    company=company,
                    created_by=session.get('name') or session.get('user') or '',
                ))

            db.session.commit()
            flash(
                'Petty cash allocation recorded.' if transaction_type == 'ALLOCATION'
                else 'Petty cash expense recorded.',
                'success',
            )
        except ValueError as exc:
            db.session.rollback()
            flash(str(exc), 'danger')
        return redirect(url_for('accounts_petty_cash'))

    current_entries = PettyCashEntry.query.filter_by(month_key=current_month).all()
    balances = {'Canon': 0.0, 'Haram': 0.0}
    for entry in current_entries:
        if entry.transaction_type == 'ALLOCATION':
            balances[entry.company] += entry.amount
        elif entry.transaction_type == 'EXPENSE':
            balances[entry.company] -= entry.amount
    balances = {company: round(max(amount, 0.0), 2) for company, amount in balances.items()}
    entries = PettyCashEntry.query.order_by(
        PettyCashEntry.date.desc(), PettyCashEntry.id.desc()
    ).limit(200).all()
    return render_template(
        'petty_cash.html',
        entries=entries,
        balances=balances,
        total_balance=round(sum(balances.values()), 2),
        current_month=current_month,
        current_month_label=datetime.strptime(current_month, '%Y-%m').strftime('%B %Y'),
        today=now.strftime('%Y-%m-%d'),
    )


@app.route('/factory-in-out-ledger', methods=['GET', 'POST'])
def factory_in_out_ledger():
    if session.get('role') not in ('owner', 'manager', 'assistant_manager'):
        return redirect(url_for('index'))

    return_target = (request.values.get('next') or '').strip()
    parsed_return_target = urlparse(return_target)
    if not (
        return_target
        and parsed_return_target.scheme == ''
        and parsed_return_target.netloc == ''
        and parsed_return_target.path.startswith('/')
        and not parsed_return_target.path.startswith('//')
        and '\\' not in return_target
    ):
        return_target = url_for('owner_dashboard' if session.get('role') == 'owner' else 'manager_dashboard')

    if request.method == 'POST':
        direction_value = (request.form.get('movement_direction') or '').strip().upper()
        date_value = (request.form.get('movement_date') or '').strip()
        item_value = (request.form.get('movement_item') or '').strip()
        unit_value = (request.form.get('movement_unit') or '').strip()
        quantity_value = parse_numeric(request.form.get('movement_quantity'))
        parsed_date = normalize_date(date_value)
        if direction_value not in ('IN', 'OUT'):
            flash('Choose whether this movement is IN or OUT.', 'danger')
        elif not parsed_date:
            flash('Enter a valid movement date.', 'danger')
        elif not item_value:
            flash('Enter an item for this movement.', 'danger')
        elif quantity_value <= 0 or not math.isfinite(quantity_value):
            flash('Quantity must be greater than zero.', 'danger')
        elif not unit_value:
            flash('Enter a unit for this movement.', 'danger')
        else:
            db.session.add(FactoryManualMovement(
                date=parsed_date.strftime('%Y-%m-%d'),
                direction=direction_value,
                item=item_value,
                description=(request.form.get('movement_description') or '').strip(),
                reference=(request.form.get('movement_reference') or '').strip(),
                quantity=quantity_value,
                unit=unit_value,
                created_by=session.get('name') or session.get('user') or '',
            ))
            db.session.commit()
            flash('Manual factory movement recorded.', 'success')
        return redirect(url_for(
            'factory_in_out_ledger',
            next=return_target,
            q=request.form.get('q', ''),
            direction=request.form.get('direction', 'ALL'),
            start_date=request.form.get('start_date', ''),
            end_date=request.form.get('end_date', ''),
        ))

    ensure_shipment_challans()
    movements = []

    def quantity_text(value):
        quantity = parse_numeric(value)
        if quantity <= 0:
            return ''
        rounded = round(quantity, 2)
        return f'{int(rounded):,}' if rounded.is_integer() else f'{rounded:,.2f}'

    def add_movement(
        date_value, direction, category, item, description, reference, quantity,
        unit, quantity_display=None, recorded_at=None,
    ):
        if quantity_display is None and parse_numeric(quantity) <= 0:
            return
        quantity_display = quantity_display or f'{quantity_text(quantity)} {unit}'.strip()
        if not quantity_display:
            return
        if isinstance(date_value, datetime):
            date_value = date_value.strftime('%Y-%m-%d')
        date_text = str(date_value or '').strip()
        parsed_date = normalize_date(date_text)
        movements.append({
            'sort_date': parsed_date or datetime.min,
            'sort_recorded_at': ledger_recorded_at(recorded_at, date_value),
            'date': parsed_date.strftime('%d/%m/%Y') if parsed_date else (date_text or 'â€”'),
            'direction': direction,
            'category': category,
            'item': item or 'â€”',
            'description': description or 'â€”',
            'reference': reference or 'â€”',
            'quantity': quantity_display,
        })

    received_serials = set()
    for receipt in ReceivingChallan.query.order_by(ReceivingChallan.id.asc()).all():
        if receipt.serial_no:
            received_serials.add(receipt.serial_no.strip().casefold())
        fabric_name = receipt.fabric_for or receipt.fabric_quality or 'Fabric'
        reference = receipt.challan_no or receipt.serial_no or f'Receiving #{receipt.id}'
        for field, quality in (('fabric_qty_a', 'A quality'), ('fabric_qty_b', 'B quality')):
            quantity = getattr(receipt, field, None)
            if parse_numeric(quantity) > 0:
                add_movement(
                    receipt.recv_date,
                    'IN',
                    'Fabric received',
                    fabric_name,
                    quality,
                    reference,
                    quantity,
                    'MTR',
                    recorded_at=receipt.created_at,
                )
        if parse_numeric(receipt.received_cut_pcs) > 0:
            add_movement(
                receipt.recv_date,
                'IN',
                'Fabric received',
                fabric_name,
                'Cut pieces',
                reference,
                receipt.received_cut_pcs,
                'PCS',
                recorded_at=receipt.created_at,
            )

    for inventory in Inventory.query.order_by(Inventory.id.asc()).all():
        if inventory.serial_no and inventory.serial_no.strip().casefold() in received_serials:
            continue
        reference = inventory.challan_no or inventory.serial_no or f'Inventory #{inventory.id}'
        if inventory.item_name and parse_numeric(inventory.quantity) > 0:
            add_movement(
                inventory.recv_date,
                'IN',
                'Inventory received',
                inventory.item_name,
                inventory.received_from or inventory.suppliers,
                reference,
                inventory.quantity,
                inventory.unit or 'PCS',
                recorded_at=inventory.created_at,
            )
            continue
        fabric_name = inventory.fabric_for or inventory.fabric_quality or 'Fabric'
        for field, quality in (('fabric_qty_a', 'A quality'), ('fabric_qty_b', 'B quality')):
            quantity = getattr(inventory, field, None)
            if parse_numeric(quantity) > 0:
                add_movement(
                    inventory.recv_date,
                    'IN',
                    'Inventory received',
                    fabric_name,
                    quality,
                    reference,
                    quantity,
                    'MTR',
                    recorded_at=inventory.created_at,
                )

    accessories = SavedRequirement.query.order_by(SavedRequirement.id.asc()).all()
    accessories_by_id = {item.id: item for item in accessories}
    for item in accessories:
        supplier_returns = item.supplier_returns
        received_qty = (
            accessory_layer_received_qty(item)
            + sum(parse_numeric(entry.returned_qty) for entry in supplier_returns)
        )
        if accessory_layer_received_qty(item) > 0:
            add_movement(
                item.received_at or item.po_sent_at,
                'IN',
                'Accessory received',
                item.item,
                ' · '.join(value for value in (item.size, item.quality, item.supplier) if value),
                f'PO {item.po_no}' if item.po_no else f'Requirement #{item.id}',
                received_qty,
                item.unit or 'PCS',
                recorded_at=item.created_at,
            )
        for supplier_return in supplier_returns:
            is_exchange = (
                (supplier_return.return_type or '').strip().upper() == 'EXCHANGE'
            )
            supplier_return_reference = (
                f'PO {item.po_no} - EXCHANGE #{supplier_return.id}'
                if is_exchange and item.po_no
                else f'Requirement #{item.id} - EXCHANGE #{supplier_return.id}'
                if is_exchange
                else f'PO {item.po_no}' if item.po_no else f'Requirement #{item.id}'
            )
            if is_exchange:
                add_movement(
                    supplier_return.return_date,
                    'IN',
                    'Accessory supplier exchange received',
                    supplier_return.exchange_item or item.item,
                    supplier_return.note or item.supplier,
                    supplier_return_reference,
                    supplier_return.returned_qty,
                    supplier_return.exchange_item_unit or item.unit or 'PCS',
                    recorded_at=supplier_return.created_at,
                )
                add_movement(
                    supplier_return.return_date,
                    'OUT',
                    'Accessory supplier exchange accepted',
                    item.item,
                    supplier_return.note or item.supplier,
                    supplier_return_reference,
                    supplier_return.returned_qty,
                    item.unit or 'PCS',
                    recorded_at=supplier_return.created_at,
                )
            else:
                add_movement(
                    supplier_return.return_date,
                    'OUT',
                    f'Accessory supplier {supplier_return.return_type.lower()}',
                    item.item,
                    supplier_return.note or item.supplier,
                    supplier_return_reference,
                    supplier_return.returned_qty,
                    item.unit or 'PCS',
                    recorded_at=supplier_return.created_at,
                )
        if item.issue_entries:
            for issue in item.issue_entries:
                add_movement(
                    issue.issue_date,
                    'OUT',
                    'Accessory issued',
                    item.item,
                    'Issued to ' + (issue.worker_name or 'worker'),
                    f'PO {item.po_no}' if item.po_no else f'Requirement #{item.id}',
                    issue.issued_qty,
                    item.unit or 'PCS',
                    recorded_at=issue.created_at,
                )
        elif parse_numeric(item.issued_qty) > 0:
            add_movement(
                item.received_at or item.date,
                'OUT',
                'Accessory issued',
                item.item,
                'Legacy issue record',
                f'PO {item.po_no}' if item.po_no else f'Requirement #{item.id}',
                item.issued_qty,
                item.unit or 'PCS',
                recorded_at=item.created_at,
            )

    challans = ChallanRecord.query.order_by(ChallanRecord.id.asc()).all()
    standalone_return_ids = {
        challan.inventory_id
        for challan in challans
        if challan.source_type == 'inventory_return' and challan.inventory_id
    }
    for challan in challans:
        if challan.source_type not in ('order', 'inventory_return'):
            continue
        quantities = []
        pieces = parse_numeric(challan.shipped_pcs)
        if pieces <= 0:
            pieces = parse_numeric(challan.shipped_aq_pcs) + parse_numeric(challan.shipped_bq_pcs)
        if pieces > 0:
            quantities.append(f'{quantity_text(pieces)} PCS')
        for field, unit in (
            ('shipped_packets', 'PACKETS'),
            ('shipped_ctn', 'CTN'),
            ('shipped_bails', 'BAILS'),
            ('shipped_meter', 'MTR'),
        ):
            display_quantity = quantity_text(getattr(challan, field, 0))
            if display_quantity:
                quantities.append(f'{display_quantity} {unit}')
        if quantities:
            add_movement(
                challan.challan_date,
                'OUT',
                'Goods dispatched',
                challan.article_name or 'Factory goods',
                challan.party_name,
                challan.challan_no,
                0,
                '',
                quantity_display=' · '.join(quantities),
                recorded_at=challan.created_at,
            )

        try:
            combined_inventory_ids = json.loads(challan.combined_inventory_ids or '[]')
        except (TypeError, ValueError):
            combined_inventory_ids = []
        if challan.source_type == 'order':
            for inventory_id in combined_inventory_ids:
                if inventory_id in standalone_return_ids:
                    continue
                inventory = db.session.get(Inventory, inventory_id)
                if not inventory or not inventory.b_returned_to_party or not inventory.b_returned_shipped:
                    continue
                add_movement(
                    inventory.b_returned_shipped_date or challan.challan_date,
                    'OUT',
                    'Returned fabric dispatched',
                    inventory.b_returned_article or inventory.fabric_for or 'Returned fabric',
                    inventory.b_returned_party or challan.party_name,
                    challan.challan_no,
                    inventory.b_returned_quantity,
                    'MTR',
                    recorded_at=inventory.created_at,
                )

    for movement in FactoryManualMovement.query.order_by(FactoryManualMovement.id.asc()).all():
        add_movement(
            movement.date,
            movement.direction,
            'Manual entry',
            movement.item,
            movement.description,
            movement.reference,
            movement.quantity,
            movement.unit,
            recorded_at=movement.created_at,
        )

    search = (request.args.get('q') or '').strip().casefold()
    direction = (request.args.get('direction') or 'ALL').upper()
    if direction not in ('ALL', 'IN', 'OUT'):
        direction = 'ALL'
    start_text = (request.args.get('start_date') or '').strip()
    end_text = (request.args.get('end_date') or '').strip()
    start_date = normalize_date(start_text)
    end_date = normalize_date(end_text)
    visible_movements = [
        movement for movement in movements
        if (direction == 'ALL' or movement['direction'] == direction)
        and (not start_date or movement['sort_date'] >= start_date)
        and (not end_date or movement['sort_date'] <= end_date.replace(hour=23, minute=59, second=59))
        and (
            not search
            or search in ' '.join(str(movement[key]) for key in ('date', 'category', 'item', 'description', 'reference', 'quantity', 'direction')).casefold()
        )
    ]
    visible_movements.sort(
        key=lambda movement: movement['sort_recorded_at'],
        reverse=True,
    )
    return render_template(
        'factory_in_out_ledger.html',
        movements=visible_movements,
        direction=direction,
        search=request.args.get('q', ''),
        start_date=start_text,
        end_date=end_text,
        return_url=return_target,
        today=datetime.utcnow().strftime('%Y-%m-%d'),
    )


@app.route('/accounts/accessories-billing')
def accounts_accessories_billing():
    denied = accounts_management_access('accounts')
    if denied:
        return denied

    search = (request.args.get('q') or '').strip().casefold()
    requirements = SavedRequirement.query.filter(
        SavedRequirement.bill_amount.isnot(None),
        func.trim(SavedRequirement.bill_amount) != '',
    ).order_by(SavedRequirement.id.desc()).all()
    rows = []
    total_billed = 0.0
    for requirement in requirements:
        if search and not any(
            search in (value or '').casefold()
            for value in (
                requirement.supplier,
                requirement.item,
                requirement.order_id,
                requirement.po_no,
            )
        ):
            continue
        order = Order.query.filter_by(job_no=requirement.order_id).first() if requirement.order_id else None
        bill_amount = parse_numeric(requirement.bill_amount)
        total_billed += bill_amount
        rows.append({'requirement': requirement, 'order': order, 'bill_amount': bill_amount})
    return render_template(
        'accessory_billing.html',
        rows=rows,
        search=request.args.get('q', ''),
        total_billed=total_billed,
    )


@app.route('/accounts/utility-bills', methods=['GET', 'POST'])
def accounts_utility_bills():
    denied = accounts_management_access('accounts')
    if denied:
        return denied

    utility_types = ('Electricity', 'Gas', 'Water', 'R.O WATER', 'Internet', 'Telephone', 'Other')
    payment_methods = ('Cash', 'Bank Transfer', 'Cheque', 'Other')
    if request.method == 'POST':
        action = request.form.get('action', '')
        if action == 'create_bill':
            utility_type = (request.form.get('utility_type') or '').strip()
            company = (request.form.get('company') or 'Canon').strip().title()
            provider = (request.form.get('provider') or '').strip()
            account_reference = (request.form.get('account_reference') or '').strip()
            billing_period = (request.form.get('billing_period') or '').strip()
            bill_date = (request.form.get('bill_date') or '').strip()
            due_date = (request.form.get('due_date') or '').strip()
            try:
                if utility_type not in utility_types:
                    raise ValueError('Select a valid utility type.')
                if company not in ('Canon', 'Haram'):
                    raise ValueError('Select Canon or Haram for this bill.')
                if not provider:
                    raise ValueError('Provider is required.')
                if not re.fullmatch(r'\d{4}-(0[1-9]|1[0-2])', billing_period):
                    raise ValueError('Billing period must be a valid month.')
                datetime.strptime(bill_date, '%Y-%m-%d')
                if due_date:
                    datetime.strptime(due_date, '%Y-%m-%d')
                amount = parse_billing_amount(request.form.get('amount'), 'Bill amount')
                if amount <= 0:
                    raise ValueError('Bill amount must be greater than zero.')
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect(url_for('accounts_utility_bills'))
            db.session.add(UtilityBill(
                utility_type=utility_type,
                provider=provider,
                account_reference=account_reference,
                billing_period=billing_period,
                bill_date=bill_date,
                due_date=due_date,
                amount=amount,
                company=company,
                notes=(request.form.get('notes') or '').strip(),
                created_by=session.get('name') or session.get('user') or '',
            ))
            db.session.commit()
            flash('Utility bill recorded.', 'success')
            return redirect(url_for('accounts_utility_bills'))

        if action == 'record_payment':
            bill = UtilityBill.query.get(request.form.get('bill_id', type=int))
            if not bill:
                flash('Utility bill not found.', 'danger')
                return redirect(url_for('accounts_utility_bills'))
            tid = (request.form.get('tid') or '').strip()[:100]
            cheque_number = (request.form.get('cheque_number') or '').strip()[:100]
            proof_upload = request.files.get('proof_of_payment')
            cheque_upload = request.files.get('cheque_image')
            proof_filename = ''
            cheque_filename = ''
            try:
                amount = parse_billing_amount(request.form.get('amount'), 'Payment amount')
                paid_on = (request.form.get('paid_on') or '').strip()
                datetime.strptime(paid_on, '%Y-%m-%d')
                paid_total = sum(payment.amount for payment in bill.payments)
                balance = round(bill.amount - paid_total, 2)
                if amount <= 0:
                    raise ValueError('Payment amount must be greater than zero.')
                if amount > balance:
                    raise ValueError(f'Payment cannot exceed the remaining balance of PKR {balance:,.2f}.')
                method = (request.form.get('method') or '').strip()
                if method not in payment_methods:
                    raise ValueError('Select a valid payment method.')
                if method == 'Bank Transfer':
                    if not tid:
                        raise ValueError('Enter the TID for the bank transfer.')
                    if not proof_upload or not proof_upload.filename:
                        raise ValueError('Upload proof of payment for the bank transfer.')
                    proof_extension = proof_upload.filename.rsplit('.', 1)[-1].lower() if '.' in proof_upload.filename else ''
                    if proof_extension not in {'png', 'jpg', 'jpeg', 'webp', 'pdf'}:
                        raise ValueError('Upload the proof as a PNG, JPG, WEBP, or PDF file.')
                    safe_name = secure_filename(proof_upload.filename)
                    if not safe_name:
                        raise ValueError('Choose a valid proof-of-payment file.')
                    proof_filename = f"utility_payment_proof_{datetime.utcnow().strftime('%Y%m%d%H%M%S%f')}_{safe_name}"
                elif method == 'Cheque':
                    if not cheque_number:
                        raise ValueError('Enter the cheque number.')
                    if not cheque_upload or not cheque_upload.filename:
                        raise ValueError('Upload a picture of the cheque.')
                    cheque_extension = cheque_upload.filename.rsplit('.', 1)[-1].lower() if '.' in cheque_upload.filename else ''
                    if cheque_extension not in {'png', 'jpg', 'jpeg', 'webp'}:
                        raise ValueError('Upload the cheque picture as a PNG, JPG, or WEBP image.')
                    safe_name = secure_filename(cheque_upload.filename)
                    if not safe_name:
                        raise ValueError('Choose a valid cheque image file.')
                    cheque_filename = f"utility_payment_cheque_{datetime.utcnow().strftime('%Y%m%d%H%M%S%f')}_{safe_name}"
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect(url_for('accounts_utility_bills'))
            if proof_filename:
                proof_upload.save(os.path.join(app.config['UPLOAD_FOLDER'], proof_filename))
            if cheque_filename:
                cheque_upload.save(os.path.join(app.config['UPLOAD_FOLDER'], cheque_filename))
            db.session.add(UtilityBillPayment(
                bill_id=bill.id,
                amount=amount,
                paid_on=paid_on,
                method=method,
                reference=(request.form.get('reference') or '').strip(),
                tid=tid,
                proof_of_payment=f'/static/uploads/{proof_filename}' if proof_filename else '',
                cheque_number=cheque_number,
                cheque_image=f'/static/uploads/{cheque_filename}' if cheque_filename else '',
                notes=(request.form.get('payment_notes') or '').strip(),
                paid_by=session.get('name') or session.get('user') or '',
            ))
            db.session.commit()
            flash('Utility bill payment recorded.', 'success')
            return redirect(url_for('accounts_utility_bills'))

        flash('Choose a valid utility-bill action.', 'danger')
        return redirect(url_for('accounts_utility_bills'))

    search = (request.args.get('q') or '').strip().casefold()
    bills = UtilityBill.query.order_by(UtilityBill.billing_period.desc(), UtilityBill.due_date.desc(), UtilityBill.id.desc()).all()
    latest_summaries = {}
    for summary in UtilityBillSummary.query.order_by(UtilityBillSummary.id.desc()).all():
        latest_summaries.setdefault(summary.utility_bill_id, summary)
    today = datetime.utcnow().strftime('%Y-%m-%d')
    current_month = datetime.utcnow().strftime('%Y-%m')
    rows = []
    totals = {'amount': 0.0, 'paid': 0.0, 'balance': 0.0}
    for bill in bills:
        if search and not any(search in (value or '').casefold() for value in (bill.utility_type, bill.provider, bill.account_reference, bill.billing_period)):
            continue
        paid = round(sum(payment.amount for payment in bill.payments), 2)
        balance = round(max(bill.amount - paid, 0.0), 2)
        summary = latest_summaries.get(bill.id)
        summary_rows = json.loads(summary.rows_json or '[]') if summary else []
        if not summary_rows:
            summary_rows = [None]
        group_status = (
            'PAID' if balance <= 0 else
            'PARTIAL' if paid > 0 else
            'UNPAID' if summary else
            'OVERDUE' if bill.due_date and bill.due_date < today else
            'UNPAID'
        )
        remaining_paid = paid
        for index, summary_row in enumerate(summary_rows):
            amount = round(float(summary_row.get('total') or 0), 2) if summary_row else round(bill.amount, 2)
            row_paid = min(amount, remaining_paid)
            remaining_paid = max(remaining_paid - row_paid, 0.0)
            row_balance = round(max(amount - row_paid, 0.0), 2)
            status = (
                'PAID' if row_balance <= 0 else
                'PARTIAL' if row_paid > 0 else
                'UNPAID' if summary else
                'OVERDUE' if bill.due_date and bill.due_date < today else
                'UNPAID'
            )
            rows.append({
                'bill': bill,
                'amount': amount,
                'paid': row_paid,
                'balance': row_balance,
                'payment_balance': balance,
                'payment_owner': index == 0,
                'group_size': len(summary_rows),
                'group_paid': paid,
                'group_balance': balance,
                'group_status': group_status,
                'status': status,
                'summary': summary,
                'summary_row': summary_row,
            })
        totals['amount'] += bill.amount
        totals['paid'] += paid
        totals['balance'] += balance
    return render_template(
        'utility_bills.html',
        rows=rows,
        totals=totals,
        search=request.args.get('q', ''),
        today=today,
        current_month=current_month,
        utility_types=utility_types,
        payment_methods=payment_methods,
    )


UTILITY_BILL_BANKS = (
    'Al Baraka Bank (Pakistan) Limited',
    'Allied Bank Limited',
    'Apna Microfinance Bank Limited',
    'Askari Bank Limited',
    'Bank Alfalah Limited',
    'Bank AL Habib Limited',
    'Bank of Azad Jammu and Kashmir',
    'Bank of China Limited',
    'Bank of Khyber',
    'Bank of Punjab',
    'BankIslami Pakistan Limited',
    'Citibank N.A.',
    'Deutsche Bank AG',
    'Dubai Islamic Bank Pakistan Limited',
    'Faysal Bank Limited',
    'First Women Bank Limited',
    'Habib Bank Limited',
    'Habib Metropolitan Bank Limited',
    'HBL Microfinance Bank Limited',
    'Industrial and Commercial Bank of China Limited',
    'JS Bank Limited',
    'Khushhali Microfinance Bank Limited',
    'LOLC Microfinance Bank Limited',
    'MCB Bank Limited',
    'MCB Islamic Bank Limited',
    'Meezan Bank Limited',
    'Mobilink Microfinance Bank Limited',
    'MUFG Bank Limited',
    'National Bank of Pakistan',
    'NRSP Microfinance Bank Limited',
    'Pak Oman Microfinance Bank Limited',
    'Punjab Provincial Cooperative Bank Limited',
    'Samba Bank Limited',
    'Sindh Bank Limited',
    'Sindh Microfinance Bank Limited',
    'Soneri Bank Limited',
    'Standard Chartered Bank (Pakistan) Limited',
    'Telenor Microfinance Bank Limited',
    'U Microfinance Bank Limited',
    'United Bank Limited',
    'Zarai Taraqiati Bank Limited',
)


def next_utility_bill_voucher_no():
    stored_numbers = UtilityBillSummary.query.with_entities(UtilityBillSummary.invoice_no).filter(
        UtilityBillSummary.invoice_no.isnot(None)
    ).all()
    voucher_numbers = []
    for (invoice_no,) in stored_numbers:
        if not invoice_no:
            continue
        if invoice_no.isdigit():
            voucher_numbers.append(int(invoice_no))
            continue
        legacy_match = re.fullmatch(r'UBS-\d{4}-(\d+)', invoice_no)
        if legacy_match:
            voucher_numbers.append(int(legacy_match.group(1)))
    highest_number = max(voucher_numbers, default=0)
    return f'{highest_number + 1:04d}'


def normalize_utility_bill_voucher_no(summary):
    legacy_match = re.fullmatch(r'UBS-\d{4}-(\d+)', summary.invoice_no or '')
    if not legacy_match:
        return False
    summary.invoice_no = f'{int(legacy_match.group(1)):04d}'
    return True


@app.route('/accounts/utility-bill-summary', methods=['GET', 'POST'])
def accounts_utility_bill_summary():
    denied = accounts_management_access('accounts')
    if denied:
        return denied

    summary_id = request.values.get('summary_id', type=int)
    bill_id = request.values.get('bill_id', type=int)
    summary = UtilityBillSummary.query.get(summary_id) if summary_id else None
    if summary_id and not summary:
        abort(404)
    if not summary and bill_id:
        summary = UtilityBillSummary.query.filter_by(utility_bill_id=bill_id).order_by(UtilityBillSummary.id.desc()).first()
    bill = summary.utility_bill if summary else None
    today = datetime.utcnow().strftime('%Y-%m-%d')
    utility_types = ('Electricity', 'Gas', 'Water', 'R.O WATER', 'Internet', 'Telephone', 'Other')

    if request.method == 'POST':
        action = request.form.get('action', '')
        if action not in ('save_summary', 'create_invoice'):
            abort(400)
        utility_type = (request.form.get('utility_type') or '').strip()
        company = (request.form.get('company') or 'Canon').strip().title()
        provider = (request.form.get('provider') or '').strip()
        account_reference = (request.form.get('account_reference') or '').strip()
        bank_name = (request.form.get('bank_name') or '').strip()
        billing_period = (request.form.get('billing_period') or '').strip()
        bill_date = (request.form.get('bill_date') or '').strip()
        due_date = (request.form.get('due_date') or '').strip()

        row_fields = (
            'meter_no', 'bill_no', 'location', 'previous_reading', 'present_reading', 'units', 'electric_charges',
            'adjustment', 'fuel_charges', 'additional_surcharge', 'tariff_difference',
            'maintenance_charges', 'water_charges',
        )
        row_values = {field: request.form.getlist(field) for field in row_fields}
        row_count = max((len(values) for values in row_values.values()), default=0)
        summary_rows = []
        cheque_upload = request.files.get('cheque_image')
        cheque_filename = ''
        try:
            if utility_type not in utility_types:
                raise ValueError('Select a valid utility type.')
            if company not in ('Canon', 'Haram'):
                raise ValueError('Select Canon or Haram for this bill.')
            if not provider:
                raise ValueError('Provider is required.')
            if not re.fullmatch(r'\d{4}-(0[1-9]|1[0-2])', billing_period):
                raise ValueError('Billing period must be a valid month.')
            datetime.strptime(bill_date, '%Y-%m-%d')
            if due_date:
                datetime.strptime(due_date, '%Y-%m-%d')
            if cheque_upload and cheque_upload.filename:
                extension = cheque_upload.filename.rsplit('.', 1)[-1].lower() if '.' in cheque_upload.filename else ''
                if extension not in {'png', 'jpg', 'jpeg', 'webp'}:
                    raise ValueError('Upload the cheque as a PNG, JPG, or WEBP image.')
                safe_name = secure_filename(cheque_upload.filename)
                if not safe_name:
                    raise ValueError('Choose a valid cheque image file.')
                cheque_filename = f"{datetime.utcnow().strftime('%Y%m%d%H%M%S%f')}_{safe_name}"
            for index in range(row_count):
                raw = {field: values[index].strip() if index < len(values) else '' for field, values in row_values.items()}
                if not any(raw.values()):
                    continue
                if not raw['meter_no']:
                    raise ValueError(f'Meter number is required for row {index + 1}.')
                numbers = {}
                for field in row_fields[3:]:
                    value = raw[field] or '0'
                    try:
                        numbers[field] = float(value.replace(',', ''))
                    except ValueError as exc:
                        raise ValueError(f'Enter a valid number for {field.replace("_", " ")} in row {index + 1}.') from exc
                    if not math.isfinite(numbers[field]):
                        raise ValueError(f'Enter a valid number for {field.replace("_", " ")} in row {index + 1}.')
                if numbers['units'] == 0 and numbers['present_reading'] >= numbers['previous_reading']:
                    numbers['units'] = numbers['present_reading'] - numbers['previous_reading']
                total_electric_charges = numbers['electric_charges'] + sum(
                    numbers[field] for field in (
                        'adjustment', 'fuel_charges', 'additional_surcharge', 'tariff_difference',
                    )
                )
                line_total = total_electric_charges + numbers['maintenance_charges'] + numbers['water_charges']
                rate = total_electric_charges / numbers['units'] if numbers['units'] else 0
                summary_rows.append({
                    **raw,
                    **numbers,
                    'rate': round(rate, 2),
                    'total_electric_charges': round(total_electric_charges, 2),
                    'total': round(line_total, 2),
                })
            if not summary_rows:
                raise ValueError('Add at least one meter row to the summary.')
            invoice_date = (request.form.get('invoice_date') or '').strip()
            if bank_name and bank_name not in UTILITY_BILL_BANKS:
                raise ValueError('Select a valid bank.')
            if action == 'create_invoice':
                if not (request.form.get('invoice_to') or '').strip():
                    raise ValueError('Enter who this invoice is for.')
                if not bank_name:
                    raise ValueError('Select a bank.')
                datetime.strptime(invoice_date, '%Y-%m-%d')
                if not cheque_filename and not (summary and summary.cheque_image):
                    raise ValueError('Upload the cheque image before generating the invoice.')
        except ValueError as exc:
            flash(str(exc), 'danger')
            return redirect(url_for('accounts_utility_bill_summary', summary_id=summary.id if summary else None, bill_id=bill.id if bill else None))

        if not bill:
            bill = UtilityBill(
                utility_type=utility_type,
                provider=provider,
                account_reference=account_reference,
                billing_period=billing_period,
                bill_date=bill_date,
                due_date=due_date,
                amount=0.0,
                company=company,
                created_by=session.get('name') or session.get('user') or '',
            )
            db.session.add(bill)
            db.session.flush()
            summary = UtilityBillSummary(utility_bill_id=bill.id)
        else:
            bill.utility_type = utility_type
            bill.company = company
            bill.provider = provider
            bill.account_reference = account_reference
            bill.billing_period = billing_period
            bill.bill_date = bill_date
            bill.due_date = due_date

        summary.title = (request.form.get('title') or bill.provider or 'Utility Bill Summary').strip()[:200]
        summary.invoice_to = (request.form.get('invoice_to') or '').strip()[:200]
        summary.bank_name = bank_name
        summary.invoice_date = invoice_date if action == 'create_invoice' else (summary.invoice_date or today)
        if cheque_filename:
            cheque_upload.save(os.path.join(app.config['UPLOAD_FOLDER'], cheque_filename))
            summary.cheque_image = f'/static/uploads/{cheque_filename}'
        summary.rows_json = json.dumps(summary_rows)
        summary.total_amount = round(sum(row['total'] for row in summary_rows), 2)
        bill.amount = summary.total_amount
        summary.notes = (request.form.get('notes') or '').strip()[:500]
        summary.created_by = summary.created_by or session.get('name') or session.get('user') or ''
        db.session.add(summary)
        db.session.flush()
        normalize_utility_bill_voucher_no(summary)
        if action == 'create_invoice' and not summary.invoice_no:
            summary.invoice_no = next_utility_bill_voucher_no()
        db.session.commit()
        flash('Bill summary saved.' if action == 'save_summary' else 'Invoice created from the bill summary.', 'success')
        return redirect(url_for('accounts_utility_bill_summary', summary_id=summary.id, view='invoice' if action == 'create_invoice' else None))

    if summary:
        bill = summary.utility_bill
        summary_rows = json.loads(summary.rows_json or '[]')
    else:
        summary_rows = []
    normalized_current_number = normalize_utility_bill_voucher_no(summary) if summary else False
    summaries = UtilityBillSummary.query.order_by(UtilityBillSummary.created_at.desc(), UtilityBillSummary.id.desc()).limit(100).all()
    normalized_list_numbers = [normalize_utility_bill_voucher_no(item) for item in summaries]
    if normalized_current_number or any(normalized_list_numbers):
        db.session.commit()
    return render_template(
        'utility_bill_summary.html',
        summary=summary,
        bill=bill,
        summary_rows=summary_rows or [{}],
        summaries=summaries,
        utility_types=utility_types,
        bank_names=UTILITY_BILL_BANKS,
        today=today,
        current_month=datetime.utcnow().strftime('%Y-%m'),
        view=request.args.get('view', 'edit'),
    )


@app.route('/accounts/utility-bill-summary/<int:summary_id>/print/<string:document_type>')
def print_utility_bill_summary(summary_id, document_type):
    denied = accounts_management_access('accounts')
    if denied:
        return denied
    if document_type not in ('summary', 'invoice'):
        abort(404)
    summary = UtilityBillSummary.query.get_or_404(summary_id)
    if document_type == 'invoice' and not summary.invoice_no:
        abort(404)
    if normalize_utility_bill_voucher_no(summary):
        db.session.commit()
    bill = summary.utility_bill
    print_time = datetime.now(timezone(timedelta(hours=5), name='PKT'))
    try:
        billing_month_display = datetime.strptime(bill.billing_period or '', '%Y-%m').strftime('%b-%y').upper()
    except ValueError:
        billing_month_display = bill.billing_period or ''
    try:
        prd_date_display = datetime.strptime(bill.bill_date or '', '%Y-%m-%d').strftime('%d-%m-%Y')
    except ValueError:
        prd_date_display = bill.bill_date or ''
    template_name = 'utility_bill_voucher_print.html' if document_type == 'invoice' else 'utility_bill_summary_print.html'
    template_context = {
        'summary': summary,
        'bill': bill,
        'billing_month_display': billing_month_display,
        'prd_date_display': prd_date_display,
        'summary_rows': json.loads(summary.rows_json or '[]'),
        'document_type': document_type,
        'prepared_by': session.get('name') or session.get('user') or 'System',
        'print_timestamp': f"{print_time.strftime('%A, %B')} {print_time.day}, {print_time.strftime('%Y at %I:%M %p')}",
        'company_name': 'HARAM ENTERPRISES' if summary.utility_bill.company == 'Haram' else 'CANON ENTERPRISES',
        'company_logo_screen': 'haram-black.png' if summary.utility_bill.company == 'Haram' else 'canon logo black.webp',
        'company_logo_print': 'haram-black.png' if summary.utility_bill.company == 'Haram' else 'canon logo black.webp',
        'bank_name': summary.bank_name or bill.provider,
    }
    if document_type == 'invoice':
        template_context.update(
            amount_words=amount_in_words(summary.total_amount, indian=True),
            cheque_image_url=summary.cheque_image,
        )
    return render_template(
        template_name,
        **template_context,
    )


@app.route('/accounts/utility-bills/<int:bill_id>/invoice')
def utility_bill_invoice(bill_id):
    denied = accounts_management_access('accounts')
    if denied:
        return denied

    bill = UtilityBill.query.get_or_404(bill_id)
    payments = sorted(bill.payments, key=lambda payment: (payment.paid_on or '', payment.created_at or datetime.min))
    total_paid = round(sum(payment.amount for payment in payments), 2)
    if bill.amount <= 0 or total_paid < round(bill.amount, 2):
        flash('The invoice is available after the bill is fully paid.', 'warning')
        return redirect(url_for('accounts_utility_bills'))

    latest_payment = payments[-1]
    summary = UtilityBillSummary.query.filter_by(utility_bill_id=bill.id).order_by(UtilityBillSummary.id.desc()).first()
    if summary:
        normalize_utility_bill_voucher_no(summary)
        if not summary.invoice_no:
            summary.invoice_no = next_utility_bill_voucher_no()
        if not summary.invoice_date:
            summary.invoice_date = latest_payment.paid_on or bill.bill_date
        invoice_summary = summary
        summary_rows = json.loads(summary.rows_json or '[]')
    else:
        summary_rows = [{
            'meter_no': bill.account_reference or '',
            'bill_no': bill.provider,
            'location': bill.utility_type,
            'total': bill.amount,
        }]
        invoice_summary = UtilityBillSummary(
            utility_bill_id=bill.id,
            title=f'{bill.utility_type} Bill Summary',
            invoice_date=latest_payment.paid_on or bill.bill_date,
            invoice_to=bill.company,
            invoice_no=next_utility_bill_voucher_no(),
            rows_json=json.dumps(summary_rows),
            total_amount=bill.amount,
            notes=bill.notes or '',
            created_by=bill.created_by or '',
        )
        db.session.add(invoice_summary)
        summary = invoice_summary
    db.session.commit()

    if not summary_rows:
        summary_rows = [{
            'meter_no': bill.account_reference or '',
            'bill_no': bill.provider,
            'location': bill.utility_type,
            'total': bill.amount,
        }]
    cheque_payment = next((payment for payment in reversed(payments) if payment.cheque_image), None)
    cheque_image_url = cheque_payment.cheque_image if cheque_payment else (summary.cheque_image if summary else '')
    return render_template(
        'utility_bill_voucher_print.html',
        summary=invoice_summary,
        bill=bill,
        summary_rows=summary_rows,
        company_name='HARAM ENTERPRISES' if bill.company == 'Haram' else 'CANON ENTERPRISES',
        company_logo_screen='haram-black.png' if bill.company == 'Haram' else 'canon logo black.webp',
        company_logo_print='haram-black.png' if bill.company == 'Haram' else 'canon logo black.webp',
        amount_words=amount_in_words(bill.amount, indian=True),
        cheque_image_url=cheque_image_url,
        cheque_no=latest_payment.cheque_number or latest_payment.tid or '',
        payment_date=latest_payment.paid_on,
        payment_reference_label='PAYMENT REF',
        payment_method_label='BANK' if summary and summary.bank_name else 'METHOD',
        bank_name=summary.bank_name if summary and summary.bank_name else latest_payment.method,
        invoice_title='UTILITY BILL PAYMENT INVOICE',
        invoice_back_url=url_for('accounts_utility_bills'),
        print_timestamp=datetime.now().strftime('%m/%d/%Y / %I:%M %p'),
    )


@app.route('/accounts/yearly-closing')
def accounts_yearly_closing():
    if not owner_only():
        return redirect(url_for('login', target_role='owner', next=url_for('accounts_yearly_closing')))
    return redirect(url_for('annual_reports'))

def format_article_no(number: int) -> str:
    return f"ART-{number:03d}"


def normalize_article_no(article_no):
    if not article_no:
        return None
    text = str(article_no).strip().upper()
    match = re.match(r'^(?:ART-)?0*(\d+)$', text)
    if match:
        return f"{int(match.group(1)):03d}"
    return text


def display_article_no(article_no):
    if not article_no:
        return ''
    text = str(article_no).strip().upper()
    match = re.match(r'^(?:ART-)?0*(\d+)$', text)
    if match:
        return format_article_no(int(match.group(1)))
    return text


def get_linked_article_order_filters(order):
    filters = []
    if order.article_id:
        filters.append(Order.article_id == order.article_id)
    if order.article:
        filters.extend((
            func.lower(Order.article) == func.lower(order.article),
            func.lower(Order.article) == func.lower(display_article_no(order.article)),
        ))
    return filters


def orders_share_article(source_order, destination_order):
    filters = get_linked_article_order_filters(source_order)
    return bool(
        filters
        and Order.query.filter(
            Order.id == destination_order.id,
            or_(*filters),
        ).first()
    )


def generate_article_no():
    last_article = Article.query.order_by(Article.id.desc()).first()
    if not last_article or not last_article.article_no:
        return normalize_article_no('1')

    match = re.search(r'^(?:ART-)?0*(\d+)$', (last_article.article_no or '').upper())
    if not match:
        return normalize_article_no('1')

    next_num = int(match.group(1)) + 1
    return normalize_article_no(str(next_num))


def get_latest_order_for_article(article_ref):
    if article_ref is None:
        return None

    if isinstance(article_ref, Article):
        article_obj = article_ref
    elif isinstance(article_ref, int):
        article_obj = Article.query.get(article_ref)
    else:
        article_obj = Article.query.filter_by(article_no=str(article_ref)).first()

    if not article_obj:
        return None

    latest_order = Order.query.filter_by(article_id=article_obj.id).order_by(Order.id.desc()).first()
    if latest_order:
        return latest_order

    return Order.query.filter_by(article=article_obj.article_no).order_by(Order.id.desc()).first()

@app.route('/manager/dashboard', methods=['GET', 'POST'])
def manager_dashboard():
    if not session.get('role'):
        return redirect(url_for('index'))

    active_tab = request.args.get('tab') or request.form.get('active_tab') or 'list'
    filter_job = request.args.get('filter_job') or request.form.get('filter_job', '')
    filter_cut = request.args.get('filter_cut') or request.form.get('filter_cut', '')
    filter_worker = request.args.get('filter_worker') or request.form.get('filter_worker', '')
    selected_month = request.args.get('payout_month') or request.form.get('payout_month') or datetime.now().strftime('%Y-%m')
    selected_week = request.args.get('payout_week') or request.form.get('payout_week') or '1-14'

    editing_order = None
    edit_order_id = request.args.get('edit_order_id') or request.form.get('edit_order_id')
    if is_read_only_profile():
        edit_order_id = None
    if edit_order_id:
        db.session.remove()
        editing_order = Order.query.get(edit_order_id)

    article_search = (request.args.get('article_search') or request.form.get('article_search', '')).strip()
    selected_head_party = (request.args.get('head_party') or '').strip()
    selected_head_article_name = (request.args.get('head_article_name') or '').strip()
    selected_head_article_no = (request.args.get('head_article_no') or '').strip()
    selected_head_color = (request.args.get('head_color') or '').strip()
    selected_head = {
        'party': selected_head_party,
        'article_name': selected_head_article_name,
        'article_no': selected_head_article_no,
        'color': selected_head_color,
    }
    selected_article_id = request.args.get('selected_article_id') or request.form.get('selected_article_id')
    selected_article = Article.query.get(selected_article_id) if selected_article_id else None

    prefill_order_id = request.args.get('prefill_order_id') or request.form.get('prefill_order_id')
    if prefill_order_id:
        session_id = db.session().bind
        db.session.remove()
        prefill_order = Order.query.get(prefill_order_id)
        if session_id is not None:
            db.session.bind = session_id
    else:
        prefill_order = None

    if editing_order:
        form_order = editing_order
    elif selected_article:
        latest_order = get_latest_order_for_article(selected_article)
        if latest_order:
            form_order = SimpleNamespace(
                id=latest_order.id,
                date=latest_order.date,
                po_no=latest_order.po_no,
                file_no=latest_order.file_no,
                name=latest_order.name,
                article=latest_order.article,
                article_name=latest_order.article_name or selected_article.article_name,
                style=latest_order.style,
                color=latest_order.color,
                qty=latest_order.qty,
                new_qty_dozen=latest_order.new_qty_dozen,
                new_qty_pcs=latest_order.new_qty_pcs,
                body_size=latest_order.body_size,
                cut_size=latest_order.cut_size,
                sample=latest_order.sample,
                fab_width=latest_order.fab_width,
                fab=latest_order.fab,
                usage=latest_order.usage,
                margin=(selected_article.margin if selected_article and selected_article.margin else latest_order.margin),
                pcs_per_side=(selected_article.pcs_per_side if selected_article and selected_article.pcs_per_side else latest_order.pcs_per_side),
                label=latest_order.label,
                label_1=latest_order.label_1,
                label_2=latest_order.label_2,
                label_3=latest_order.label_3,
                rn=latest_order.rn,
                wash=latest_order.wash,
                logo=latest_order.logo,
                emb=latest_order.emb,
                print_field=latest_order.print_field,
                poly_size=latest_order.poly_size,
                pcs_poly=latest_order.pcs_poly,
                pkt_ctn=latest_order.pkt_ctn,
                ctn_size=latest_order.ctn_size,
                ctn_label=latest_order.ctn_label,
                barcode=latest_order.barcode,
                qty_ctn=latest_order.qty_ctn,
                qty_bail=latest_order.qty_bail,
                net_w=latest_order.net_w,
                net_w_bail=latest_order.net_w_bail,
                gross_w=latest_order.gross_w,
                gross_w_bail=latest_order.gross_w_bail,
                total_ctn=latest_order.total_ctn,
                total_bails=latest_order.total_bails,
                ship_date=latest_order.ship_date,
                challan=latest_order.challan,
                image_file=latest_order.image_file,
                image_files=latest_order.image_files,
                article_id=selected_article.id,
            )
        else:
            form_order = SimpleNamespace(
                id=None,
                date='',
                po_no='',
                file_no='',
                name=selected_article.party_name or '',
                article=selected_article.article_no,
                article_name=selected_article.article_name or '',
                style=selected_article.style or '',
                color=selected_article.color or '',
                qty='',
                    new_qty_dozen='',
                    new_qty_pcs='',
                body_size='',
                cut_size='',
                sample='',
                fab_width='',
                fab='',
                usage='',
                margin=selected_article.margin if selected_article else '',
                pcs_per_side=selected_article.pcs_per_side if selected_article else '',
                label='',
                label_1='',
                label_2='',
                label_3='',
                rn='',
                wash='',
                logo='',
                emb='',
                print_field='',
                poly_size='',
                pcs_poly='',
                pkt_ctn='',
                ctn_size='',
                ctn_label='',
                barcode='',
                qty_ctn='',
                qty_bail='',
                net_w='',
                net_w_bail='',
                gross_w='',
                gross_w_bail='',
                total_ctn='',
                total_bails='',
                ship_date='',
                challan='',
                image_file='',
                image_files='[]',
                article_id=selected_article.id,
            )
    elif prefill_order:
        form_order = SimpleNamespace(
            id=prefill_order.id,
            date=prefill_order.date,
            po_no=prefill_order.po_no,
            file_no=prefill_order.file_no,
            name=prefill_order.name,
            article=prefill_order.article,
            article_name=prefill_order.article_name,
            style=prefill_order.style,
            color=prefill_order.color,
            qty=prefill_order.qty,
            new_qty_dozen=prefill_order.new_qty_dozen,
            new_qty_pcs=prefill_order.new_qty_pcs,
            body_size=prefill_order.body_size,
            cut_size=prefill_order.cut_size,
            sample=prefill_order.sample,
            fab_width=prefill_order.fab_width,
            fab=prefill_order.fab,
            usage=prefill_order.usage,
            margin=prefill_order.margin,
            label=prefill_order.label,
            label_1=prefill_order.label_1,
            label_2=prefill_order.label_2,
            label_3=prefill_order.label_3,
            rn=prefill_order.rn,
            wash=prefill_order.wash,
            logo=prefill_order.logo,
            emb=prefill_order.emb,
            print_field=prefill_order.print_field,
            poly_size=prefill_order.poly_size,
            pcs_poly=prefill_order.pcs_poly,
            pkt_ctn=prefill_order.pkt_ctn,
            ctn_size=prefill_order.ctn_size,
            ctn_label=prefill_order.ctn_label,
            barcode=prefill_order.barcode,
            qty_ctn=prefill_order.qty_ctn,
            qty_bail=prefill_order.qty_bail,
            net_w=prefill_order.net_w,
            net_w_bail=prefill_order.net_w_bail,
            gross_w=prefill_order.gross_w,
            gross_w_bail=prefill_order.gross_w_bail,
            total_ctn=prefill_order.total_ctn,
            total_bails=prefill_order.total_bails,
            ship_date=prefill_order.ship_date,
            challan=prefill_order.challan,
            image_file=prefill_order.image_file,
            image_files=prefill_order.image_files,
            article_id=prefill_order.article_id,
        )
    else:
        form_order = None

    if request.method == 'POST':
        form_action = request.form.get('form_action')

        if form_action == 'add_party':
            order_id = request.form.get('order_id')
            order_entry = Order.query.get(order_id) if order_id else None
            if order_entry and is_read_only_profile():
                return reject_read_only_edit()
            selected_article_id = request.form.get('selected_article_id') or request.args.get('selected_article_id')
            selected_article = Article.query.get(selected_article_id) if selected_article_id else None

            if order_entry:
                order_entry.date = request.form.get('date') or request.form.get('start_date')
                order_entry.file_no = f"FILE-{request.form.get('file_no', '').strip()}"
                order_entry.cut_no = request.form.get('cut_no', '')
                article_name = (request.form.get('article_name') or request.form.get('item_name') or '').strip()
                party_name = (request.form.get('party_name') or '').strip().upper()
                style_value = (request.form.get('style') or '').strip()
                color_value = (request.form.get('color') or request.form.get('colour') or '').strip()

                normalized_article = normalize_article_no(order_entry.article)
                article_record = selected_article or Article.query.get(order_entry.article_id) or Article.query.filter_by(article_no=normalized_article).first()
                if not article_record and normalized_article:
                    article_record = Article(article_no=normalized_article, article_name=article_name, party_name=party_name, color=color_value, style=style_value)
                    db.session.add(article_record)
                    db.session.flush()

                order_entry.name = party_name or order_entry.name
                order_entry.article = (article_record.article_no if article_record else normalized_article) or generate_article_no()
                order_entry.article = normalize_article_no(order_entry.article)
                order_entry.article_id = article_record.id if article_record else order_entry.article_id

                if article_record:
                    order_entry.article_name = article_record.article_name or article_name or order_entry.article_name
                    order_entry.style = article_record.style or style_value or order_entry.style
                    order_entry.color = article_record.color or color_value or order_entry.color
                else:
                    order_entry.article_name = article_name or order_entry.article_name
                    order_entry.style = style_value or order_entry.style
                    order_entry.color = color_value or order_entry.color
                order_entry.qty = request.form.get('qty') or request.form.get('order_qty', '')
                extension_pcs_text = request.form.get('extension_order_pcs', '').strip()
                order_entry.pcs_per_side = request.form.get('pcs_per_side', '') or (article_record.pcs_per_side if article_record else '')
                try:
                    current_pcs = max(0.0, float(order_entry.new_qty_pcs or order_entry.qty or 0))
                except (TypeError, ValueError):
                    current_pcs = 0.0
                try:
                    extension_pcs = max(0.0, float(extension_pcs_text or 0))
                except ValueError:
                    extension_pcs = 0.0
                try:
                    previous_extension = max(0.0, float(order_entry.extension_order_pcs or 0))
                except (TypeError, ValueError):
                    previous_extension = 0.0
                base_pcs = max(0.0, current_pcs - previous_extension)
                updated_pcs = round(base_pcs + extension_pcs)
                order_entry.extension_order_pcs = str(round(extension_pcs))
                order_entry.new_qty_pcs = str(updated_pcs)
                order_entry.new_qty_dozen = str(round(updated_pcs / 12, 3))
                order_entry.qty = str(updated_pcs)
                order_entry.year = request.form.get('year', '')
                order_entry.body_size = request.form.get('body_size', '')
                order_entry.cut_size = request.form.get('cut_size', '')
                order_entry.sample = request.form.get('sample', '')
                order_entry.fab_width = request.form.get('fab_width', '')
                order_entry.fab = request.form.get('fab', '')
                order_entry.usage = request.form.get('usage', '')
                order_entry.margin = request.form.get('margin', '') or (article_record.margin if article_record else '')
                order_entry.label = request.form.get('label', '')
                order_entry.label_1 = request.form.get('label_1', '')
                order_entry.label_2 = request.form.get('label_2', '')
                order_entry.label_3 = request.form.get('label_3', '')
                order_entry.rn = request.form.get('rn', '')
                order_entry.wash = request.form.get('wash', '')
                order_entry.logo = request.form.get('logo', '')
                order_entry.emb = request.form.get('emb', '')
                order_entry.print_field = request.form.get('print', '')
                order_entry.poly_size = request.form.get('poly_size', '')
                order_entry.pcs_poly = request.form.get('pcs_poly', '')

                if article_record:
                    article_record.pcs_per_side = order_entry.pcs_per_side or article_record.pcs_per_side
                    article_record.margin = order_entry.margin or article_record.margin
                    linked_orders = Order.query.filter_by(article_id=article_record.id).all()
                    for linked_order in linked_orders:
                        linked_order.pcs_per_side = article_record.pcs_per_side
                        linked_order.margin = article_record.margin
                order_entry.pkt_ctn = request.form.get('pkt_ctn', '')
                order_entry.ctn_size = request.form.get('ctn_size', '')
                order_entry.ctn_label = request.form.get('ctn_label', '')
                order_entry.barcode = request.form.get('barcode', '')
                order_entry.qty_ctn = request.form.get('qty_ctn', '')
                order_entry.qty_bail = request.form.get('qty_bail', '')
                order_entry.net_w = request.form.get('net_w', '')
                order_entry.net_w_bail = request.form.get('net_w_bail', '')
                order_entry.gross_w = request.form.get('gross_w', '')
                order_entry.gross_w_bail = request.form.get('gross_w_bail', '')
                order_entry.total_ctn = request.form.get('total_ctn', '')
                order_entry.total_bails = request.form.get('total_bails', '')
                order_entry.ship_date = request.form.get('ship_date', '')
                order_entry.challan = request.form.get('challan', '')

                save_order_images(
                    order_entry,
                    [request.files.get(f'image_file_{index}') for index in range(1, 11)]
                )

                db.session.commit()
                flash('Order updated successfully.', 'success')
                return redirect(url_for('manager_dashboard', tab='add_party'))
            else:
                article_no = selected_article.article_no if selected_article else generate_article_no()
                article_no = normalize_article_no(article_no)
                article_name = (request.form.get('article_name') or request.form.get('item_name') or '').strip()
                party_name = (request.form.get('party_name') or '').strip().upper()
                style_value = (request.form.get('style') or '').strip()
                color_value = (request.form.get('color') or request.form.get('colour') or '').strip()
                article_record = selected_article or Article.query.filter_by(article_no=article_no).first()
                if not article_record:
                    article_record = Article(
                        article_no=article_no,
                        article_name=article_name,
                        party_name=party_name,
                        color=color_value,
                        style=style_value,
                        pcs_per_side=request.form.get('pcs_per_side', ''),
                        margin=request.form.get('margin', '')
                    )
                    db.session.add(article_record)
                    db.session.flush()
                else:
                    article_record.pcs_per_side = request.form.get('pcs_per_side', '') or article_record.pcs_per_side
                    article_record.margin = request.form.get('margin', '') or article_record.margin
                pcs_per_side_value = request.form.get('pcs_per_side', '') or article_record.pcs_per_side or ''
                margin_value = request.form.get('margin', '') or article_record.margin or ''
                qty_mode = request.form.get('qty_input_mode', '')
                submitted_dozen = request.form.get('new_qty_dozen', '').strip()
                submitted_pcs = request.form.get('new_qty_pcs', '').strip()
                if qty_mode == 'dozen' and submitted_dozen:
                    try:
                        dozens = max(0.0, float(submitted_dozen))
                    except ValueError:
                        dozens = 0.0
                    normalized_dozen = submitted_dozen
                    normalized_pcs = str(round(dozens * 12))
                    normalized_qty = str(round(dozens * 12))
                elif qty_mode == 'pcs' and submitted_pcs:
                    try:
                        pcs = max(0.0, float(submitted_pcs))
                    except ValueError:
                        pcs = 0.0
                    normalized_dozen = str(round(pcs / 12, 3))
                    normalized_pcs = submitted_pcs
                    normalized_qty = str(round(pcs))
                else:
                    normalized_dozen = submitted_dozen
                    normalized_pcs = submitted_pcs
                    normalized_qty = request.form.get('qty') or request.form.get('order_qty', '')
                new_order = Order(
                    job_no=f"ORDER-{100 + Order.query.count() + 1}",
                    date=request.form.get('date') or request.form.get('start_date'),
                    name=article_record.party_name or party_name,
                    file_no=f"FILE-{request.form.get('file_no', '').strip()}",
                    cut_no=request.form.get('cut_no', ''),
                    article=article_record.article_no,
                    article_name=article_record.article_name or article_name,
                    article_id=article_record.id,
                    po_no=request.form.get('po_no', ''),
                    style=article_record.style or style_value,
                    color=article_record.color or color_value,
                    qty=normalized_qty,
                    new_qty_dozen=normalized_dozen,
                    new_qty_pcs=normalized_pcs,
                    pcs_per_side=pcs_per_side_value,
                    year=request.form.get('year', ''),
                    body_size=request.form.get('body_size', ''),
                    cut_size=request.form.get('cut_size', ''),
                    sample=request.form.get('sample', ''),
                    fab_width=request.form.get('fab_width', ''),
                    fab=request.form.get('fab', ''),
                    usage=request.form.get('usage', ''),
                    margin=margin_value,
                    label=request.form.get('label', ''),
                    label_1=request.form.get('label_1', ''),
                    label_2=request.form.get('label_2', ''),
                    label_3=request.form.get('label_3', ''),
                    rn=request.form.get('rn', ''),
                    wash=request.form.get('wash', ''),
                    logo=request.form.get('logo', ''),
                    emb=request.form.get('emb', ''),
                    print_field=request.form.get('print', ''),
                    poly_size=request.form.get('poly_size', ''),
                    pcs_poly=request.form.get('pcs_poly', ''),
                    pkt_ctn=request.form.get('pkt_ctn', ''),
                    ctn_size=request.form.get('ctn_size', ''),
                    ctn_label=request.form.get('ctn_label', ''),
                    barcode=request.form.get('barcode', ''),
                    qty_ctn=request.form.get('qty_ctn', ''),
                    qty_bail=request.form.get('qty_bail', ''),
                    net_w=request.form.get('net_w', ''),
                    net_w_bail=request.form.get('net_w_bail', ''),
                    gross_w=request.form.get('gross_w', ''),
                    gross_w_bail=request.form.get('gross_w_bail', ''),
                    total_ctn=request.form.get('total_ctn', ''),
                    total_bails=request.form.get('total_bails', ''),
                    ship_date=request.form.get('ship_date', ''),
                    challan=request.form.get('challan', ''),
                    image_file=getattr(form_order, 'image_file', ''),
                    image_files=getattr(form_order, 'image_files', '[]'),
                )
                save_order_images(
                    new_order,
                    [request.files.get(f'image_file_{index}') for index in range(1, 11)]
                )

                db.session.add(new_order)
                db.session.commit()
                flash('Order saved successfully.', 'success')
                if is_read_only_profile():
                    return redirect(url_for('manager_dashboard', tab='add_party'))
                return redirect(url_for('manager_dashboard', tab='add_party', edit_order_id=new_order.id))

        if form_action == 'delete_party':
            if is_read_only_profile():
                return reject_read_only_edit('This profile cannot edit saved orders.')
            delete_order_id = request.form.get('delete_order_id')
            order_to_delete = Order.query.get(delete_order_id) if delete_order_id else None
            if order_to_delete:
                if delete_order_and_dependencies(order_to_delete):
                    flash('Order and all linked records deleted successfully.', 'success')
                else:
                    flash('This order has cutting transfer history. Reverse transfers before deleting it.', 'danger')
            else:
                flash('Order not found.', 'danger')
            return redirect(url_for('manager_dashboard', tab='add_party'))

        if form_action == 'delete_article':
            if is_read_only_profile():
                return reject_read_only_edit('This profile cannot edit articles.')

            article_id = request.form.get('delete_article_id', type=int)
            article_to_delete = Article.query.get(article_id) if article_id else None
            if not article_to_delete:
                flash('Article not found.', 'danger')
                return redirect(url_for('manager_dashboard', tab='list'))

            linked_orders = Order.query.filter(
                or_(
                    Order.article_id == article_to_delete.id,
                    Order.article == article_to_delete.article_no,
                    Order.article == display_article_no(article_to_delete.article_no),
                )
            ).all()
            if any(
                linked_order.job_no and CuttingTransfer.query.filter(
                    or_(
                        CuttingTransfer.source_order_id == linked_order.id,
                        CuttingTransfer.destination_order_id == linked_order.id,
                    )
                ).first()
                for linked_order in linked_orders
            ):
                flash('This article has orders with cutting transfer history. Reverse transfers before deleting it.', 'danger')
                return redirect(url_for('manager_dashboard', tab='list'))
            for linked_order in linked_orders:
                delete_order_and_dependencies(linked_order)

            ArticleOperationRate.query.filter_by(article_id=article_to_delete.id).delete(synchronize_session=False)
            CostingSheetHistory.query.filter_by(article_id=article_to_delete.id).delete(synchronize_session=False)
            db.session.delete(article_to_delete)
            db.session.commit()
            flash('Article and all linked orders deleted successfully.', 'success')
            return redirect(url_for('manager_dashboard', tab='list'))

        if form_action == 'add_worker':
            worker_name = (request.form.get('worker_name') or '').strip().upper()
            worker_email = (request.form.get('worker_email') or '').strip().lower()
            if worker_name and worker_email:
                WORKERS_DB[worker_name] = worker_email
                db.session.add(Worker(name=worker_name, email=worker_email))
                db.session.commit()
                flash(f'Worker {worker_name} added successfully.', 'success')
            else:
                flash('Please provide both worker name and email.', 'danger')
            return redirect(url_for('manager_dashboard', tab='add_worker'))

        if form_action == 'production':
            job_data = request.form.get('job_no', '')
            job_no = job_data.split('|')[0] if '|' in job_data else job_data
            party = job_data.split('|')[1] if '|' in job_data and len(job_data.split('|')) > 1 else 'N/A'
            order = Order.query.filter_by(job_no=job_no).first()
            if order:
                party = order.name

            new_log = ProductionLog(
                date=request.form.get('date'),
                job_no=job_no,
                party=party,
                article=request.form.get('article', ''),
                color=request.form.get('color', ''),
                file_no=request.form.get('file_no', ''),
                cut_no=request.form.get('cut_no', ''),
                cut_size=request.form.get('cut_size', ''),
                worker=request.form.get('worker', ''),
                operation=request.form.get('operation', ''),
                pcs=int(request.form.get('pcs', 0) or 0),
                bq_unstitch=int(parse_numeric(request.form.get('bq_unstitch', 0)))
            )
            db.session.add(new_log)
            db.session.commit()
            flash(f'Production entry saved for {job_no}.', 'success')
            return redirect(url_for('manager_dashboard', tab='production'))

        if form_action == 'filter_summary':
            filter_job = request.form.get('filter_job', '')
            filter_cut = request.form.get('filter_cut', '')
            return redirect(url_for('manager_dashboard', tab='summary_sheet', filter_job=filter_job, filter_cut=filter_cut))

        if form_action == 'filter_job_sheet':
            filter_worker = request.form.get('filter_worker', '')
            return redirect(url_for('manager_dashboard', tab='job_sheet', filter_worker=filter_worker))

        if form_action == 'filter_payout':
            selected_month = request.form.get('payout_month', selected_month)
            selected_week = request.form.get('payout_week', selected_week)
            return redirect(url_for('manager_dashboard', tab='payout_sheet', payout_month=selected_month, payout_week=selected_week))

    all_orders = Order.query.order_by(Order.id.desc()).all()
    article_query = Article.query.order_by(Article.id.desc())
    if active_tab == 'list' and article_search:
        search_term = f"%{article_search.lower()}%"
        article_query = article_query.filter(
            or_(
                func.lower(Article.article_no).like(search_term),
                func.lower(Article.article_name).like(search_term),
                func.lower(Article.party_name).like(search_term),
                func.lower(Article.color).like(search_term),
                func.lower(Article.style).like(search_term),
            )
        )

    head_filters = []
    if active_tab == 'list':
        if selected_head_party:
            head_filters.append(func.lower(func.trim(Article.party_name)) == selected_head_party.strip().lower())
        if selected_head_article_name:
            head_filters.append(func.lower(func.trim(Article.article_name)) == selected_head_article_name.strip().lower())
        if selected_head_color:
            head_filters.append(func.lower(func.trim(Article.color)) == selected_head_color.strip().lower())
        if head_filters:
            article_query = article_query.filter(and_(*head_filters))

    article_heads = []
    seen_heads = set()
    if active_tab == 'list':
        search_text = article_search.lower() if article_search else ''
        for article in Article.query.order_by(Article.id.desc()).all():
            if search_text:
                haystack = ' '.join([
                    str(article.article_no or ''),
                    str(article.article_name or ''),
                    str(article.party_name or ''),
                    str(article.color or ''),
                    str(article.style or ''),
                ]).lower()
                if search_text not in haystack:
                    continue
            head_key = (
                (article.party_name or '').strip().lower(),
                (article.article_name or '').strip().lower(),
                (article.color or '').strip().lower(),
            )
            if head_key in seen_heads:
                continue
            seen_heads.add(head_key)
            matching_articles = Article.query.filter(
                Article.party_name.ilike(article.party_name or ''),
                Article.article_name.ilike(article.article_name or ''),
                Article.color.ilike(article.color or ''),
            ).order_by(Article.id.desc()).all()
            article_heads.append({
                'party': article.party_name or '—',
                'article_name': article.article_name or '—',
                'article_no': article.article_no or '—',
                'color': article.color or '—',
                'article_count': len(matching_articles),
            })

    head_articles = []
    if active_tab == 'list' and head_filters:
        head_articles = []
        for article in article_query.all():
            order_count = Order.query.filter_by(article_id=article.id).count()
            head_articles.append({
                'id': article.id,
                'article': article.article_no,
                'article_name': article.article_name or '',
                'name': article.party_name or '',
                'color': article.color or '',
                'style': article.style or '',
                'order_qty': order_count,
            })

    article_groups = []
    if active_tab == 'list' and head_filters:
        article_groups = head_articles
    else:
        for article in article_query.all():
            latest_order = (
                Order.query.filter_by(article_id=article.id).order_by(Order.id.desc()).first()
                or Order.query.filter_by(article=article.article_no).order_by(Order.id.desc()).first()
            )
            order_count = Order.query.filter_by(article_id=article.id).count()
            article_groups.append({
                'id': article.id,
                'article': article.article_no,
                'article_name': article.article_name or '',
                'name': article.party_name or '',
                'color': article.color or '',
                'style': article.style or '',
                'file_no': (latest_order.file_no if latest_order else '') or '',
                'order_qty': order_count,
            })
    parties = all_orders
    search_results = []
    if active_tab == 'add_party' and article_search:
        search_term = f"%{article_search.lower()}%"
        search_results = Article.query.filter(
            or_(
                func.lower(Article.article_no).like(search_term),
                func.lower(Article.article_name).like(search_term),
                func.lower(Article.party_name).like(search_term),
                func.lower(Article.color).like(search_term),
                func.lower(Article.style).like(search_term),
            )
        ).order_by(Article.id.desc()).all()

    logs = ProductionLog.query.order_by(ProductionLog.id.desc()).all()
    workers = sorted(WORKERS_DB.keys())
    workers_full = WORKERS_DB

    if filter_job:
        selected_cuts = sorted({log.cut_no for log in logs if log.job_no == filter_job and log.cut_no})
    else:
        selected_cuts = []

    filtered_logs = []
    for log in logs:
        if not log.date:
            continue
        log_date = str(log.date)
        if not log_date.startswith(selected_month):
            continue
        day = int(log_date[8:10])
        if selected_week == '1-14' and day > 14:
            continue
        if selected_week == '15-30' and day < 15:
            continue
        filtered_logs.append(log)

    payout_data = []
    worker_totals = {}
    for log in filtered_logs:
        rate = get_rate_for_log(log)
        worker_totals[log.worker] = worker_totals.get(log.worker, 0) + ((log.pcs or 0) * rate)

    for worker, amount in sorted(worker_totals.items()):
        advance_total, advance_entries = get_worker_advance_summary(worker)
        payout_data.append({
            'name': worker,
            'amount': round(amount, 2),
            'adv': round(advance_total, 2),
            'bal': round(amount - advance_total, 2),
            'advance_entries': advance_entries,
        })

    saved_image_files = []
    if form_order:
        try:
            saved_image_files = json.loads(getattr(form_order, 'image_files', None) or '[]')
            if not isinstance(saved_image_files, list):
                saved_image_files = []
        except (TypeError, ValueError):
            saved_image_files = []
        if getattr(form_order, 'image_file', None) and form_order.image_file not in saved_image_files:
            saved_image_files.insert(0, form_order.image_file)

    return render_template(
        'dashboard.html',
        parties=parties,
        article_groups=article_groups,
        article_heads=article_heads,
        head_articles=head_articles,
        selected_head=selected_head,
        active_tab=active_tab,
        workers=workers,
        workers_full=workers_full,
        rates=get_rates_dict(),
        logs=logs,
        filter_job=filter_job,
        filter_cut=filter_cut,
        filter_worker=filter_worker,
        selected_month=selected_month,
        selected_week=selected_week,
        payout_data=payout_data,
        selected_cuts=selected_cuts,
        editing_order=editing_order,
        article_search=article_search,
        search_results=search_results,
        prefill_order=prefill_order,
        form_order=form_order,
        saved_image_files=saved_image_files,
        selected_article=selected_article,
        selected_article_id=selected_article.id if selected_article else '',
        article_details_locked=bool(selected_article or editing_order),
    )

# (Login route aapka pehle jaisa hi rahega, bas ADMIN_USERS ka list upar rehne dein)


@app.route('/order/<job_no>')
def order_details(job_no):
    # 'PARTIES' list ki jagah Database query ka use karein
    order = Order.query.filter_by(job_no=job_no).first()
    
    if not order: 
        flash("Order not found!", "danger")
        return redirect(url_for('manager_dashboard'))
        
    return render_template('order_details.html', order=order)


@app.route('/stock-portal/accessories/cut-data')
def accessory_cut_data():
    if not stock_portal_access_required():
        return jsonify({'error': 'Unauthorized'}), 403

    order_id = (request.args.get('order_id') or '').strip()
    item_id = request.args.get('item_id', type=int)
    if not order_id or not item_id:
        return jsonify({'error': 'Order and accessory item are required.'}), 400

    order = Order.query.filter_by(job_no=order_id).first()
    item = db.session.get(SavedRequirement, item_id)
    if not order or not item:
        return jsonify({'error': 'Order or accessory item was not found.'}), 404

    order_pcs = get_effective_order_quantity(order)
    if order_pcs <= 0:
        return jsonify({'error': 'The order has no valid piece quantity.'}), 400
    has_article_spec = (
        not order.article_id or article_material_spec_for_item(order, item.item) is not None
    )

    editing_issue_id = request.args.get('issue_id', type=int)
    editing_issue = None
    if editing_issue_id:
        editing_issue = db.session.get(AccessoryIssue, editing_issue_id)
        if (
            not editing_issue
            or editing_issue.requirement_id != item.id
            or editing_issue.order_id != order_id
        ):
            return jsonify({'error': 'Issue entry was not found for this order and item.'}), 404

    cut_rows = []
    issue_unit = (item.issue_unit or item.unit or 'PCS').strip()
    stock_unit = (item.unit or '').strip()
    stock_per_issue_unit = (
        parse_numeric(item.issue_unit_factor) or 1.0
        if issue_unit.casefold() != stock_unit.casefold()
        else 1.0
    )
    for sheet in CuttingSheet.query.filter_by(order_id=order_id).order_by(CuttingSheet.id.asc()).all():
        cutting_pcs = accessory_cut_pcs(sheet)
        if cutting_pcs <= 0:
            continue
        allowed_qty = accessory_required_qty_for_cut(item, order, cutting_pcs)
        issue_rows = AccessoryIssue.query.filter_by(
            requirement_id=item.id,
            order_id=order_id,
            cut_sheet_id=sheet.id,
        ).all()
        issued_net = 0.0
        current_gross = 0.0
        current_returned = 0.0
        for issue in issue_rows:
            if editing_issue and issue.id == editing_issue.id:
                current_gross = parse_numeric(issue.issued_qty)
                current_returned = accessory_issue_returned_qty(issue)
                continue
            issued_net += max(
                0.0,
                parse_numeric(issue.issued_qty) - accessory_issue_returned_qty(issue),
            )
        remaining_qty = max(0.0, allowed_qty - issued_net)
        cut_rows.append({
            'id': sheet.id,
            'cut_no': sheet.cut_no or str(sheet.id),
            'cutting_pcs': cutting_pcs,
            'required_qty': allowed_qty / stock_per_issue_unit,
            'issued_qty': issued_net / stock_per_issue_unit,
            'remaining_qty': remaining_qty / stock_per_issue_unit,
            'current_issue_qty': current_gross / stock_per_issue_unit,
            'current_returned_qty': current_returned / stock_per_issue_unit,
            'unit': issue_unit,
            'unplanned': not has_article_spec,
        })

    return jsonify({'cuts': cut_rows})


@app.route('/order/<job_no>/accessories')
def order_accessories(job_no):
    if not session.get('role'):
        return redirect(url_for('index'))

    order = Order.query.filter_by(job_no=job_no).first()
    if not order:
        flash('Order not found.', 'danger')
        return redirect(url_for('manager_dashboard'))

    order_qty = get_effective_order_quantity(order)

    accessory_groups = {}
    issue_rows = AccessoryIssue.query.filter_by(order_id=job_no).order_by(AccessoryIssue.id.asc()).all()
    material_specs = ArticleMaterialSpec.query.filter_by(article_id=order.article_id).order_by(
        ArticleMaterialSpec.sort_order.asc(), ArticleMaterialSpec.id.asc()
    ).all() if order.article_id else []
    for spec in material_specs:
        order_requirement = SavedRequirement.query.filter(
            SavedRequirement.order_id == job_no,
            func.lower(func.trim(SavedRequirement.item)) == (spec.item_name or '').strip().casefold(),
        ).order_by(SavedRequirement.id.asc()).first()
        spec_size = (spec.size or '').strip().casefold()
        spec_quality = (spec.material or '').strip().casefold()
        matching_issue_requirements = [
            issue.requirement for issue in issue_rows
            if issue.requirement
            and (issue.requirement.item or '').strip().casefold() == (spec.item_name or '').strip().casefold()
            and (issue.requirement.size or '').strip().casefold() == spec_size
            and (issue.requirement.quality or '').strip().casefold() == spec_quality
        ]
        stock_requirement = next(
            (requirement for requirement in matching_issue_requirements
             if accessory_layer_received_qty(requirement) > 0),
            None,
        )
        if not stock_requirement:
            matching_receipts = SavedRequirement.query.filter(
                func.lower(func.trim(SavedRequirement.item)) == (spec.item_name or '').strip().casefold(),
            ).order_by(SavedRequirement.id.asc()).all()
            stock_requirement = next((
                requirement for requirement in matching_receipts
                if (requirement.size or '').strip().casefold() == (spec.size or '').strip().casefold()
                and (requirement.quality or '').strip().casefold() == (spec.material or '').strip().casefold()
                and accessory_layer_received_qty(requirement) > 0
            ), None)
        if not stock_requirement:
            stock_requirement = order_requirement
        requirement_unit = stock_requirement.unit if stock_requirement else spec.unit
        roll_length_m = stock_requirement.roll_length_m if stock_requirement else 0.0
        group_item = stock_requirement.item if stock_requirement else spec.item_name
        group_size = stock_requirement.size if stock_requirement else spec.size
        group_quality = stock_requirement.quality if stock_requirement else spec.material
        received_qty = accessory_layer_received_qty(stock_requirement) if stock_requirement else 0.0
        item_master = ItemMaster.query.filter(
            func.lower(func.trim(ItemMaster.item_name)) == (spec.item_name or '').strip().casefold()
        ).first()
        display_unit = (
            ((item_master.issue_unit or '').strip() if item_master else '')
            or ((stock_requirement.issue_unit or '').strip() if stock_requirement else '')
            or requirement_unit
            or spec.unit
            or ''
        )
        display_factor = (
            parse_numeric(stock_requirement.issue_unit_factor) or 1.0
            if stock_requirement and received_qty > 0 and display_unit.casefold() == (stock_requirement.issue_unit or '').strip().casefold()
            else unit_conversion_factor(requirement_unit, display_unit) or 1.0
            if stock_requirement and display_unit.casefold() != (requirement_unit or '').casefold()
            else parse_numeric(item_master.issue_unit_factor) or 1.0
            if item_master and display_unit.casefold() != (requirement_unit or '').casefold()
            else 1.0
        )
        key = accessory_stock_key(group_item, group_size, group_quality, display_unit)
        group = accessory_groups.setdefault(key, {
            'item': group_item or 'UNSPECIFIED',
            'size': group_size or '',
            'quality': group_quality or '',
            'unit': display_unit,
            'display_unit': display_unit,
            'display_factor': 1.0,
            'display_issued': 0.0,
            'display_returned': 0.0,
            'roll_length_m': roll_length_m,
            'required': 0.0,
            'issued': 0.0,
            'returned': 0.0,
            'net_issued': 0.0,
            'cost': 0.0,
            'sort_order': spec.sort_order or 0,
        })
        required_qty = (
            accessory_usage_stock_qty(
                stock_requirement, order_qty * parse_numeric(spec.qty_per_piece), spec.unit
            )
            if stock_requirement else order_qty * parse_numeric(spec.qty_per_piece)
        )
        if stock_requirement and is_roll_unit(stock_requirement.unit) and roll_length_m > 0:
            required_qty = math.ceil(required_qty - 1e-10)
        elif stock_requirement:
            required_qty = round_accessory_qty_to_issue_unit(stock_requirement, required_qty)
        group['required'] += required_qty / display_factor

    for issue in issue_rows:
        receipt = issue.requirement
        if not receipt:
            continue
        display_unit = issue.issued_as_unit or receipt.issue_unit or receipt.unit or ''
        key = accessory_stock_key(receipt.item, receipt.size, receipt.quality, display_unit)
        group = accessory_groups.setdefault(key, {
            'item': receipt.item or 'UNSPECIFIED',
            'size': receipt.size or '',
            'quality': receipt.quality or '',
            'unit': display_unit,
            'display_unit': display_unit,
            'display_factor': 1.0,
            'display_issued': 0.0,
            'display_returned': 0.0,
            'roll_length_m': parse_numeric(receipt.roll_length_m),
            'required': 0.0,
            'issued': 0.0,
            'returned': 0.0,
            'net_issued': 0.0,
            'cost': 0.0,
            'sort_order': 999999,
        })
        issued_qty = parse_numeric(issue.issued_qty)
        returned_qty = accessory_issue_returned_qty(issue)
        net_issued_qty = max(0.0, issued_qty - returned_qty)
        unit_rate = accessory_receipt_unit_rate(receipt) or parse_numeric(issue.unit_rate)
        group['cost'] += net_issued_qty * unit_rate
        display_factor = parse_numeric(issue.issue_conversion_factor) or parse_numeric(receipt.issue_unit_factor) or 1.0
        entered_qty = parse_numeric(issue.issued_as_qty)
        display_issued = (
            entered_qty
            if entered_qty > 0 and (issue.issued_as_unit or '').strip().casefold() == display_unit.strip().casefold()
            else issued_qty / display_factor
        )
        display_returned = returned_qty / display_factor
        group['issued'] += display_issued
        group['returned'] += display_returned
        group['net_issued'] += max(0.0, display_issued - display_returned)
        group['display_issued'] += display_issued
        group['display_returned'] += display_returned

    accessories = []
    for group in accessory_groups.values():
        required = group['required']
        issued = group['issued']
        net_issued = group['net_issued']
        group['remaining'] = max(0.0, required - net_issued)
        group['rate'] = group['cost'] / net_issued if net_issued > 0 else 0.0
        group['display_required'] = required
        group['display_net_issued'] = max(0.0, group['display_issued'] - group['display_returned'])
        group['display_remaining'] = max(0.0, group['display_required'] - group['display_net_issued'])
        group['display_rate'] = group['cost'] / group['display_net_issued'] if group['display_net_issued'] > 0 else 0.0
        if required <= 0 and net_issued > 0:
            group['status'] = 'Unplanned'
        elif net_issued <= 0:
            group['status'] = 'Pending'
        elif net_issued + 0.000001 >= required:
            group['status'] = 'Completed'
        else:
            group['status'] = 'Partially Issued'
        accessories.append(group)
    accessories.sort(key=lambda row: (row['sort_order'], row['item'].casefold(), row['size'].casefold()))

    def quantity_summary(field):
        totals_by_unit = {}
        for row in accessories:
            quantity = row[field]
            if quantity <= 0:
                continue
            unit = row['display_unit'] or 'UNSPECIFIED'
            totals_by_unit[unit] = totals_by_unit.get(unit, 0.0) + quantity
        return [
            {'unit': unit, 'quantity': quantity}
            for unit, quantity in sorted(totals_by_unit.items(), key=lambda pair: pair[0].casefold())
        ]

    totals = {
        'required': quantity_summary('display_required'),
        'issued': quantity_summary('display_net_issued'),
        'remaining': quantity_summary('display_remaining'),
        'cost': sum(row['cost'] for row in accessories),
    }
    cut_accessories = []
    for sheet in CuttingSheet.query.filter_by(order_id=job_no).order_by(CuttingSheet.id.asc()).all():
        cutting_pcs = accessory_cut_pcs(sheet)
        if cutting_pcs <= 0:
            continue
        cut_items = build_cut_accessory_rows(order, sheet)
        required_items = [item for item in cut_items if item['required'] > 0.000001]
        if required_items and all(item['remaining'] <= 0.000001 for item in required_items):
            cut_status = 'Completed'
        elif any(item['net_issued'] > 0.000001 for item in required_items):
            cut_status = 'Partially Issued'
        elif not required_items and any(item['net_issued'] > 0.000001 for item in cut_items):
            cut_status = 'Unplanned'
        elif required_items:
            cut_status = 'Pending'
        else:
            cut_status = 'No Requirements'
        cut_accessories.append({
            'sheet': sheet,
            'cutting_pcs': cutting_pcs,
            'items': cut_items,
            'status': cut_status,
        })
    return render_template(
        'order_accessories.html',
        order=order,
        order_qty=order_qty,
        accessories=accessories,
        totals=totals,
        cut_accessories=cut_accessories,
    )


@app.route('/order/<job_no>/accessories/cut/<int:cut_sheet_id>/print')
def order_accessories_cut_print(job_no, cut_sheet_id):
    if not session.get('role'):
        return redirect(url_for('index'))
    order = Order.query.filter_by(job_no=job_no).first()
    cutting_sheet = CuttingSheet.query.filter_by(id=cut_sheet_id, order_id=job_no).first()
    if not order or not cutting_sheet:
        abort(404)
    return render_template(
        'order_accessories_cut_print.html',
        order=order,
        cutting_sheet=cutting_sheet,
        cutting_pcs=accessory_cut_pcs(cutting_sheet),
        items=build_cut_accessory_rows(order, cutting_sheet),
    )


@app.route('/manager/costing-sheet/save', methods=['POST'])
def save_costing_sheet():
    if not owner_only():
        return jsonify({'error': 'Unauthorized'}), 403

    payload = request.get_json(silent=True) or {}
    article_id = payload.get('article_id')
    snapshot = payload.get('snapshot')
    if not str(article_id).isdigit() or not isinstance(snapshot, dict):
        return jsonify({'error': 'Invalid costing sheet data'}), 400

    article = db.session.get(Article, int(article_id))
    if not article:
        return jsonify({'error': 'Article not found'}), 404

    for existing in CostingSheetHistory.query.filter_by(article_id=article.id).all():
        try:
            if json.loads(existing.snapshot_json or '{}') == snapshot:
                return jsonify({'success': True, 'duplicate': True, 'history_id': existing.id})
        except (TypeError, json.JSONDecodeError):
            continue

    history = CostingSheetHistory(
        article_id=article.id,
        created_by=session.get('name') or session.get('user'),
        snapshot_json=json.dumps(snapshot),
    )
    db.session.add(history)
    db.session.commit()
    return jsonify({'success': True, 'history_id': history.id})


@app.route('/manager/costing-sheet/history')
def costing_sheet_history():
    if not owner_only():
        return redirect(url_for('index'))

    history = CostingSheetHistory.query.order_by(CostingSheetHistory.created_at.desc()).all()
    return render_template('costing_sheet_history.html', history=history)


@app.route('/manager/costing-sheet/history/<int:history_id>/delete', methods=['POST'])
def delete_costing_sheet_history(history_id):
    if not owner_only():
        return redirect(url_for('index'))

    history = db.session.get(CostingSheetHistory, history_id)
    if history:
        db.session.delete(history)
        db.session.commit()
        flash('Costing sheet history deleted.', 'success')
    return redirect(url_for('costing_sheet_history'))


@app.route('/manager/costing-sheet')
def costing_sheet():
    if not owner_only():
        if session.get('role'):
            flash('The COSTING portal is available only to the owner.', 'danger')
        return redirect(url_for('index'))

    party_names = [
        party_name
        for (party_name,) in db.session.query(Article.party_name)
        .filter(Article.party_name.isnot(None), Article.party_name != '')
        .distinct()
        .order_by(Article.party_name)
        .all()
    ]
    selected_party_name = request.args.get('party_name', '').strip()
    history_id = request.args.get('history_id', '').strip()
    history_record = db.session.get(CostingSheetHistory, int(history_id)) if history_id.isdigit() else None
    article_query = Article.query
    if selected_party_name:
        article_query = article_query.filter_by(party_name=selected_party_name)
    articles = article_query.order_by(Article.article_name, Article.style, Article.color).all()
    selected_article_id = request.args.get('article_id', '').strip()
    article = Article.query.get(int(selected_article_id)) if selected_article_id.isdigit() else None
    if article and selected_party_name and article.party_name != selected_party_name:
        article = None
    saved_snapshot = None
    history_view = False
    snapshot_record = history_record
    if not snapshot_record and article:
        snapshot_record = CostingSheetHistory.query.filter_by(
            article_id=article.id
        ).order_by(CostingSheetHistory.created_at.desc()).first()
    if snapshot_record and article and snapshot_record.article_id == article.id:
        try:
            saved_snapshot = json.loads(snapshot_record.snapshot_json or '{}')
            history_view = bool(history_record)
        except (TypeError, json.JSONDecodeError):
            saved_snapshot = None
    order = article.orders[0] if article and article.orders else None
    rates = get_rates_for_article(article) if article else {}

    return render_template(
        'costing_sheet.html',
        articles=articles,
        party_names=party_names,
        selected_party_name=selected_party_name,
        article=article,
        order=order,
        rates=rates,
        selected_article_id=selected_article_id,
        saved_snapshot=saved_snapshot,
        history_view=history_view and saved_snapshot is not None,
        current_date=datetime.now().strftime('%Y-%m-%d'),
    )


@app.route('/manager/operation-rates/order/<job_no>', methods=['GET', 'POST'])
def operation_order_rates(job_no):
    if not session.get('role'):
        return redirect(url_for('index'))

    order = Order.query.filter_by(job_no=job_no).first_or_404()
    all_rates = OperationRate.query.order_by(OperationRate.operation).all()
    saved_items = OrderOperationRate.query.filter_by(order_id=order.id).order_by(
        OrderOperationRate.sort_order.asc(), OrderOperationRate.id.asc()
    ).all()
    saved_operations = {
        item.rate_id: item
        for item in saved_items
    }
    saved_rate_ids = {item.rate_id for item in saved_items}
    if saved_items:
        rates = (
            [rate for item in saved_items for rate in all_rates if rate.id == item.rate_id]
            + [rate for rate in all_rates if rate.id not in saved_rate_ids]
        )
    else:
        article = order.article_ref
        if not article and order.article:
            article = Article.query.filter_by(article_no=normalize_article_no(order.article)).first()
        article_items = ArticleOperationRate.query.filter_by(article_id=article.id).order_by(
            ArticleOperationRate.sort_order.asc(), ArticleOperationRate.id.asc()
        ).all() if article else []
        article_rate_ids = {item.rate_id for item in article_items}
        rates = (
            [rate for item in article_items for rate in all_rates if rate.id == item.rate_id]
            + [rate for rate in all_rates if rate.id not in article_rate_ids]
        )
    if request.method == 'POST':
        if is_read_only_profile() and saved_items:
            return reject_read_only_edit('This profile cannot edit order operation rates.')
        try:
            previous_operations = {
                item.rate_id: item
                for item in OrderOperationRate.query.filter_by(order_id=order.id).all()
            }
            submitted_rate_ids = request.form.getlist('operation_order')
            if not submitted_rate_ids:
                submitted_rate_ids = [str(rate.id) for rate in rates if request.form.get(f'operation_{rate.id}')]
            OrderOperationRate.query.filter_by(order_id=order.id).delete()
            for sort_order, rate_id in enumerate(submitted_rate_ids, start=1):
                rate = OperationRate.query.get(int(rate_id))
                if rate and request.form.get(f'operation_{rate.id}'):
                    override_raw = (request.form.get(f'override_{rate.id}') or '').strip()
                    override = float(override_raw) if override_raw else None
                    db.session.add(OrderOperationRate(order_id=order.id, rate_id=rate.id, override_rate=override, sort_order=sort_order))
                    previous = previous_operations.get(rate.id)
                    if override is not None and (not previous or previous.override_rate != override):
                        db.session.add(OperationRateHistory(
                            operation=rate.operation.upper(),
                            rate=override,
                            effective_date=datetime.utcnow(),
                            order_id=order.id,
                        ))
            db.session.commit()
            flash('Order operation rates saved.', 'success')
            return redirect(url_for('operation_order_rates', job_no=job_no))
        except Exception as exc:
            db.session.rollback()
            flash(f'Could not save order rates: {exc}', 'danger')

    histories = OperationRateHistory.query.filter_by(order_id=order.id).order_by(
        OperationRateHistory.effective_date.desc(), OperationRateHistory.id.desc()
    ).all()
    histories_by_operation = {}
    for history in histories:
        histories_by_operation.setdefault((history.operation or '').upper(), []).append(history)
    return render_template(
        'order_operation_rates.html',
        order=order,
        rates=rates,
        saved_operations=saved_operations,
        inherited_rates=get_rates_for_order(order),
        histories=histories,
        histories_by_operation=histories_by_operation,
    )


@app.route('/manager/operation-rates/order/<job_no>/<operation>/history')
def operation_rate_history(job_no, operation):
    if not session.get('role'):
        return redirect(url_for('index'))

    order = Order.query.filter_by(job_no=job_no).first_or_404()
    selected_operation = OperationRate.query.filter(
        func.lower(OperationRate.operation) == operation.strip().lower()
    ).first_or_404()
    histories = OperationRateHistory.query.filter_by(
        order_id=order.id,
        operation=selected_operation.operation.upper(),
    ).order_by(
        OperationRateHistory.effective_date.desc(), OperationRateHistory.id.desc()
    ).all()
    return render_template(
        'operation_rate_history.html',
        order=order,
        operation=selected_operation,
        histories=histories,
    )


@app.route('/manager/operation-rates/article/<int:article_id>/<int:rate_id>/history')
def article_operation_rate_history(article_id, rate_id):
    if not session.get('role'):
        return redirect(url_for('index'))

    article = Article.query.get_or_404(article_id)
    rate = OperationRate.query.get_or_404(rate_id)
    histories = ArticleOperationRateHistory.query.filter_by(
        article_id=article.id,
        rate_id=rate.id,
    ).order_by(
        ArticleOperationRateHistory.effective_date.desc(),
        ArticleOperationRateHistory.id.desc(),
    ).all()
    return render_template(
        'article_operation_rate_history.html',
        article=article,
        operation=rate,
        histories=histories,
    )


@app.route('/manager/operation-rates/order/<job_no>/<int:rate_id>/override', methods=['POST'])
def save_order_rate_override(job_no, rate_id):
    if not session.get('role'):
        return redirect(url_for('index'))
    if is_read_only_profile():
        return reject_read_only_edit('This profile cannot edit order operation rates.')

    order = Order.query.filter_by(job_no=job_no).first_or_404()
    rate = OperationRate.query.get_or_404(rate_id)
    saved_operation = OrderOperationRate.query.filter_by(order_id=order.id, rate_id=rate.id).first()
    if not saved_operation:
        flash(f'Select {rate.operation} and save the operations before revising its rate.', 'danger')
        return redirect(url_for('operation_order_rates', job_no=job_no))

    raw_override = (request.form.get('override_rate') or '').strip()
    try:
        override = float(raw_override) if raw_override else None
        if override is not None and override < 0:
            raise ValueError
    except ValueError:
        flash('Please enter a valid non-negative rate.', 'danger')
        return redirect(url_for('operation_order_rates', job_no=job_no))

    previous_override = saved_operation.override_rate
    saved_operation.override_rate = override
    if override is not None and override != previous_override:
        db.session.add(OperationRateHistory(
            operation=rate.operation.upper(),
            rate=override,
            effective_date=datetime.utcnow(),
            order_id=order.id,
        ))
    db.session.commit()
    flash(f'{rate.operation} rate updated successfully.', 'success')
    return redirect(url_for('operation_order_rates', job_no=job_no))

@app.route('/manager/articles/<article>/orders')
def article_orders(article):
    if not session.get('role'):
        return redirect(url_for('index'))

    search_term = (request.args.get('search') or '').strip()
    normalized_article = normalize_article_no(article)
    display_article = display_article_no(normalized_article or article)
    article_record = Article.query.filter(
        or_(
            func.lower(Article.article_no) == (normalized_article or article).lower(),
            func.lower(Article.article_no) == display_article.lower()
        )
    ).first()

    query = Order.query
    if article_record:
        query = query.filter(
            or_(
                Order.article_id == article_record.id,
                func.lower(Order.article) == (normalized_article or article).lower(),
                func.lower(Order.article) == display_article.lower()
            )
        )
    else:
        query = query.filter(
            or_(
                func.lower(Order.article) == (normalized_article or article).lower(),
                func.lower(Order.article) == display_article.lower()
            )
        )

    if search_term:
        search_like = f"%{search_term.lower()}%"
        query = query.filter(
            or_(
                func.lower(Order.job_no).like(search_like),
                func.lower(Order.article).like(search_like),
                func.lower(Order.article_name).like(search_like),
                func.lower(Order.name).like(search_like),
                func.lower(Order.color).like(search_like),
                func.lower(Order.style).like(search_like),
                func.lower(Order.date).like(search_like),
            )
        )

    article_orders_list = query.order_by(Order.id.desc()).all()

    for order in article_orders_list:
        order.display_article = display_article_no(order.article)

    head_party = (article_record.party_name if article_record and article_record.party_name else (article_orders_list[0].name if article_orders_list else '')).strip() if (article_record and article_record.party_name) or article_orders_list else ''
    head_article_name = (article_record.article_name if article_record and article_record.article_name else (article_orders_list[0].article_name if article_orders_list else '')).strip() if (article_record and article_record.article_name) or article_orders_list else ''
    head_color = (article_record.color if article_record and article_record.color else (article_orders_list[0].color if article_orders_list else '')).strip() if (article_record and article_record.color) or article_orders_list else ''

    return render_template(
        'article_orders.html',
        article_display=display_article_no(normalized_article or article),
        article_id=article_record.id if article_record else None,
        orders=article_orders_list,
        search=search_term,
        head_party=head_party,
        head_article_name=head_article_name,
        head_color=head_color,
    )

@app.route('/manager/article-head')
def article_head_detail():
    if not session.get('role'):
        return redirect(url_for('index'))

    head_party = (request.args.get('head_party') or '').strip()
    head_article_name = (request.args.get('head_article_name') or '').strip()
    head_article_no = (request.args.get('head_article_no') or '').strip()
    head_color = (request.args.get('head_color') or '').strip()

    if not any([head_party, head_article_name, head_color]):
        return redirect(url_for('manager_dashboard', tab='list'))

    filters = []
    if head_party:
        filters.append(func.lower(func.trim(Article.party_name)) == head_party.strip().lower())
    if head_article_name:
        filters.append(func.lower(func.trim(Article.article_name)) == head_article_name.strip().lower())
    if head_color:
        filters.append(func.lower(func.trim(Article.color)) == head_color.strip().lower())

    articles = Article.query.filter(and_(*filters)).order_by(Article.id.desc()).all()

    return render_template(
        'article_head_detail.html',
        articles=articles,
        head_party=head_party or '—',
        head_article_name=head_article_name or '—',
        head_article_no=head_article_no or '—',
        head_color=head_color or '—',
    )

@app.route('/logout')
def logout(): 
    session.clear()
    return redirect(url_for('index'))

def calculate_annual_report(report_year, include_comparison=True):
    """Build one JSON-safe annual report from the existing operational records."""
    month_names = [calendar.month_name[index] for index in range(1, 13)]
    orders = Order.query.order_by(Order.id.asc()).all()
    logs = ProductionLog.query.order_by(ProductionLog.id.asc()).all()
    workers = Worker.query.order_by(Worker.name.asc()).all()
    inventory_records = Inventory.query.order_by(Inventory.id.asc()).all()
    inventory_rows = InventoryRow.query.order_by(InventoryRow.id.asc()).all()
    cutting_sheets = CuttingSheet.query.order_by(CuttingSheet.id.asc()).all()
    challans = ReceivingChallan.query.order_by(ReceivingChallan.id.asc()).all()
    advances = WorkerAdvance.query.order_by(WorkerAdvance.id.asc()).all()

    def amount(value):
        return round(parse_numeric(value), 2)

    def quantity(order):
        if not order:
            return 0.0
        pieces = amount(order.new_qty_pcs)
        if not pieces:
            pieces = amount(order.new_qty_dozen) * 12
        return pieces or amount(order.qty)

    def in_year(value):
        parsed = normalize_date(value)
        return parsed if parsed and parsed.year == report_year else None

    order_by_job = {order.job_no: order for order in orders if order.job_no}
    dated_logs = [(normalize_date(log.date), log) for log in logs if normalize_date(log.date) and log.job_no]
    yearly_logs = [(date, log) for date, log in dated_logs if date.year == report_year]
    yearly_job_numbers = {log.job_no for _, log in yearly_logs}
    yearly_orders = [order for order in orders if in_year(order.date) or order.job_no in yearly_job_numbers]
    final_operation_by_job = {}
    stitched_operations = {
        (rate.operation or '').upper()
        for rate in OperationRate.query.all()
        if rate.is_stitched_operation
    }
    for order in orders:
        operation_names = list(get_rates_for_order(order))
        if order.job_no and operation_names:
            final_operation_by_job[order.job_no] = operation_names[-1].upper()
    rate_cache = {}

    def historical_rate(log):
        key = ((log.operation or '').upper(), str(log.date or ''))
        if key not in rate_cache:
            rate_cache[key] = get_rate_for_operation_at(log.operation, log.date)
        return rate_cache[key]

    logs_by_job = {}
    for _, log in yearly_logs:
        logs_by_job.setdefault(log.job_no, []).append(log)

    def order_production(order_logs):
        if order_logs:
            job_no = order_logs[0].job_no
            final_operation = final_operation_by_job.get(job_no)
            if final_operation:
                final_logs = [
                    log for log in order_logs
                    if (log.operation or '').upper() == final_operation
                ]
                raw_total = sum(max(0, int(log.pcs or 0)) for log in final_logs)
                if final_operation in stitched_operations:
                    return raw_total
                bq_total = sum(max(0, int(log.bq_unstitch or 0)) for log in final_logs)
                return max(0, raw_total - bq_total)
        operation_totals = {}
        for log in order_logs:
            operation = (log.operation or 'OTHER').upper()
            operation_totals[operation] = operation_totals.get(operation, 0) + (log.pcs or 0)
        return max(operation_totals.values(), default=0)

    completion_dates = {}
    cumulative_by_job = {}
    cumulative_final_raw = {}
    cumulative_final_bq = {}
    for date, log in sorted(dated_logs, key=lambda item: (item[0], item[1].id or 0)):
        operation = (log.operation or 'OTHER').upper()
        final_operation = final_operation_by_job.get(log.job_no)
        if final_operation:
            if operation != final_operation:
                continue
            cumulative_final_raw[log.job_no] = cumulative_final_raw.get(log.job_no, 0) + max(0, int(log.pcs or 0))
            cumulative_final_bq[log.job_no] = cumulative_final_bq.get(log.job_no, 0) + max(0, int(log.bq_unstitch or 0))
            produced_to_date = cumulative_final_raw[log.job_no]
            if final_operation not in stitched_operations:
                produced_to_date = max(0, produced_to_date - cumulative_final_bq[log.job_no])
        else:
            operation_totals = cumulative_by_job.setdefault(log.job_no, {})
            operation_totals[operation] = operation_totals.get(operation, 0) + (log.pcs or 0)
            produced_to_date = max(operation_totals.values(), default=0)
        order = order_by_job.get(log.job_no)
        if order and quantity(order) > 0 and produced_to_date >= quantity(order):
            completion_dates.setdefault(log.job_no, date)

    order_rows = []
    for order in yearly_orders:
        order_logs = logs_by_job.get(order.job_no, [])
        ordered = quantity(order)
        produced = amount(order_production(order_logs))
        progress = round(min(100.0, produced / ordered * 100), 2) if ordered else None
        completed = completion_dates.get(order.job_no)
        completed_in_year = bool(completed and completed.year == report_year)
        order_rows.append({
            'job_no': order.job_no or '-', 'party': order.name or '-',
            'article': order.article or '-', 'article_name': order.article_name or '-',
            'style': order.style or '-', 'color': order.color or '-', 'po_no': order.po_no or '-',
            'order_quantity': amount(ordered), 'produced_quantity': produced,
            'remaining_quantity': amount(max(0, ordered - produced)), 'progress': progress,
            'status': 'Completed' if completed_in_year or (ordered > 0 and produced >= ordered) else 'In Progress',
            'shipment_date': order.ship_date or '-',
        })

    monthly = []
    operation_map = {}
    worker_map = {}
    article_map = {}
    monthly_job_logs = {}
    for date, log in yearly_logs:
        month_index = date.month - 1
        monthly_job_logs.setdefault(month_index, {}).setdefault(log.job_no, []).append(log)
        operation = (log.operation or 'OTHER').upper()
        cost = amount((log.pcs or 0) * historical_rate(log))
        operation_map.setdefault(operation, {'pieces': 0, 'labor_cost': 0.0})
        operation_map[operation]['pieces'] += log.pcs or 0
        operation_map[operation]['labor_cost'] += cost
        worker_name = log.worker or 'UNKNOWN'
        worker_map.setdefault(worker_name, {'pieces': 0, 'labor_earnings': 0.0})
        worker_map[worker_name]['pieces'] += log.pcs or 0
        worker_map[worker_name]['labor_earnings'] += cost
        order = order_by_job.get(log.job_no)
        article_key = (order.article if order else None) or log.article or '-'
        article_map.setdefault(article_key or '-', {'orders': set(), 'article_name': (order.article_name if order else None) or log.article_name or '-', 'party': (order.name if order else None) or log.party or '-', 'style': (order.style if order else None) or log.order_style or '-', 'color': (order.color if order else None) or log.color or '-', 'pieces': 0, 'labor_cost': 0.0})
        article_map[article_key or '-']['orders'].add(log.job_no)
        article_map[article_key or '-']['pieces'] += log.pcs or 0
        article_map[article_key or '-']['labor_cost'] += cost

    for month_index, month_name in enumerate(month_names):
        month_logs = [log for _, log in yearly_logs if normalize_date(log.date).month - 1 == month_index]
        month_production = sum(order_production(job_logs) for job_logs in monthly_job_logs.get(month_index, {}).values())
        month_cost = sum((log.pcs or 0) * historical_rate(log) for log in month_logs)
        month_orders = {job_no for job_no, job_logs in monthly_job_logs.get(month_index, {}).items() if job_logs}
        month_completed = sum(1 for job_no, date in completion_dates.items() if date.year == report_year and date.month - 1 == month_index)
        monthly.append({'month': month_name, 'orders': len(month_orders), 'produced_pieces': amount(month_production), 'labor_cost': amount(month_cost), 'completed_orders': month_completed})

    received_records = [record for record in inventory_records if in_year(record.recv_date)]
    received = sum(amount(record.fabric_qty_a) + amount(record.fabric_qty_b) for record in received_records)
    annual_sheets = [sheet for sheet in cutting_sheets if in_year(sheet.cut_date) or (sheet.created_at and sheet.created_at.year == report_year)]
    issued = sum(amount(row.fabric_issue) for row in inventory_rows if in_year(row.date))
    used = sum(amount(sheet.total_meter) for sheet in annual_sheets)
    returned = sum(amount(row.fabric_return) for row in inventory_rows if in_year(row.date))
    wastage = sum(amount(row.wastage) for row in inventory_rows if in_year(row.date))
    fabric_balance = max(0.0, received - used + returned)
    cut_rows = [{
        'sheet_number': sheet.serial_no or str(sheet.id), 'order': sheet.order_id or '-', 'cut_no': sheet.cut_no or '-',
        'cut_quantity': amount(sheet.quantity), 'cut_size': sheet.cut_size or '-', 'fabric_meters': amount(sheet.total_meter),
        'palla': amount(sheet.total_palla), 'pieces': amount(sheet.total_pcs or sheet.summary_total_pcs),
        'cutter': sheet.cutter_name or '-', 'shortage': amount(sheet.shortage), 'inventory_serial': sheet.inventory_serial_no or '-'
    } for sheet in annual_sheets]

    annual_advances = [entry for entry in advances if in_year(entry.date)]
    total_advances = sum(amount(entry.amount) for entry in annual_advances if entry.record_type == 'advance')
    total_payments = sum(amount(entry.amount) for entry in annual_advances if entry.record_type == 'payment')
    ledger_by_worker = {}
    for entry in advances:
        signed_amount = amount(entry.amount) if entry.record_type == 'advance' else -amount(entry.amount)
        ledger_by_worker[entry.worker_id] = ledger_by_worker.get(entry.worker_id, 0.0) + signed_amount
    outstanding_advances = sum(max(0.0, ledger_by_worker.get(worker.id, 0.0)) for worker in workers)
    total_ordered = sum(row['order_quantity'] for row in order_rows)
    total_produced = sum(row['produced_quantity'] for row in order_rows)
    total_labor = sum(item['labor_cost'] for item in operation_map.values())
    completed_count = sum(1 for row in order_rows if row['status'] == 'Completed')
    active_workers = {log.worker for _, log in yearly_logs if log.worker}
    order_count = len(order_rows)
    production_progress = round(total_produced / total_ordered * 100, 2) if total_ordered else None

    party_map = {}
    for row in order_rows:
        party = row['party'] or '-'
        item = party_map.setdefault(party, {'orders': 0, 'ordered_pieces': 0.0, 'produced_pieces': 0.0, 'completed_orders': 0})
        item['orders'] += 1
        item['ordered_pieces'] += row['order_quantity']
        item['produced_pieces'] += row['produced_quantity']
        item['completed_orders'] += row['status'] == 'Completed'
    party_rows = [{**item, 'party': party, 'outstanding_orders': item['orders'] - item['completed_orders'], 'production_progress': round(item['produced_pieces'] / item['ordered_pieces'] * 100, 2) if item['ordered_pieces'] else None} for party, item in party_map.items()]
    article_rows = [{
        **item,
        'article': article,
        'orders': len(item['orders']),
        'ordered_pieces': 0.0,
        'produced_pieces': amount(sum(
            order_row['produced_quantity']
            for order_row in order_rows
            if order_row['article'] == article
        )),
        'labor_cost': amount(item['labor_cost']),
    } for article, item in article_map.items()]
    for row in article_rows:
        row['orders_set'] = None
        row['ordered_pieces'] = amount(sum(item['order_quantity'] for item in order_rows if item['article'] == row['article']))
        row.pop('orders_set', None)

    report = {
        'year': report_year, 'reporting_period': f'01 January {report_year} - 31 December {report_year}',
        'kpis': {'total_orders': order_count, 'completed_orders': completed_count, 'in_progress_orders': max(0, order_count - completed_count), 'orders_without_production': sum(1 for row in order_rows if not row['produced_quantity']), 'total_ordered_pieces': amount(total_ordered), 'total_produced_pieces': amount(total_produced), 'production_progress': production_progress, 'total_articles': len({row['article'] for row in order_rows if row['article'] != '-'}), 'total_workers': len(workers), 'active_workers': len(active_workers), 'total_labor_cost': amount(total_labor), 'total_worker_advances': amount(total_advances), 'total_worker_payments': amount(total_payments), 'outstanding_worker_advances': amount(outstanding_advances), 'fabric_received': amount(received), 'fabric_used': amount(used), 'fabric_returned': amount(returned), 'fabric_wastage': amount(wastage), 'fabric_balance': amount(fabric_balance), 'total_cuts': len(cut_rows)},
        'monthly': monthly, 'orders': order_rows, 'parties': party_rows,
        'articles': article_rows, 'operations': [{'operation': key, **value, 'labor_cost': amount(value['labor_cost'])} for key, value in sorted(operation_map.items())],
        'workers': [{'worker': key, **value, 'labor_earnings': amount(value['labor_earnings'])} for key, value in sorted(worker_map.items())],
        'cuts': cut_rows, 'fabric': {'received': amount(received), 'issued': amount(issued), 'used': amount(used), 'returned': amount(returned), 'wastage': amount(wastage), 'balance': amount(fabric_balance), 'records': len(received_records)},
        'labor': {'total': amount(total_labor), 'average_per_piece': amount(total_labor / total_produced) if total_produced else None, 'by_order': [{'order': row['job_no'], 'labor_cost': amount(sum((log.pcs or 0) * historical_rate(log) for log in logs_by_job.get(row['job_no'], [])))} for row in order_rows]},
        'advances': {'total_advances': amount(total_advances), 'total_payments': amount(total_payments), 'outstanding': amount(outstanding_advances)},
        'fabric_utilization': {'utilization_percent': round(used / received * 100, 2) if received else None, 'wastage_percent': round(wastage / received * 100, 2) if received else None, 'fabric_per_cut_piece': amount(used / sum(row['pieces'] for row in cut_rows)) if sum(row['pieces'] for row in cut_rows) else None, 'fabric_per_produced_piece': amount(used / total_produced) if total_produced else None},
        'comparison': {}, 'data_notes': []
    }
    if not order_rows:
        report['data_notes'].append('No orders were recorded during this reporting period.')
    if not yearly_logs:
        report['data_notes'].append('No production records were recorded during this reporting period.')
    if not received_records:
        report['data_notes'].append('No fabric receiving records were recorded during this reporting period.')
    if include_comparison:
        previous = calculate_annual_report(report_year - 1, include_comparison=False)
        current_metrics = {'Orders': order_count, 'Production': total_produced, 'Labor Cost': total_labor, 'Completed Orders': completed_count, 'Completion Rate': round(completed_count / order_count * 100, 2) if order_count else 0, 'Workers': len(active_workers), 'Fabric Received': received, 'Fabric Used': used, 'Cuts': len(cut_rows)}
        previous_metrics = {'Orders': previous['kpis']['total_orders'], 'Production': previous['kpis']['total_produced_pieces'], 'Labor Cost': previous['kpis']['total_labor_cost'], 'Completed Orders': previous['kpis']['completed_orders'], 'Completion Rate': round(previous['kpis']['completed_orders'] / previous['kpis']['total_orders'] * 100, 2) if previous['kpis']['total_orders'] else 0, 'Workers': previous['kpis']['active_workers'], 'Fabric Received': previous['kpis']['fabric_received'], 'Fabric Used': previous['kpis']['fabric_used'], 'Cuts': previous['kpis']['total_cuts']}
        report['comparison'] = [{'metric': key, 'previous': value, 'current': current_metrics[key], 'change': amount(current_metrics[key] - value), 'change_percent': round((current_metrics[key] - value) / value * 100, 2) if value else None} for key, value in previous_metrics.items()]
    return report


def annual_report_years():
    years = {datetime.now().year}
    for model, field in ((Order, Order.date), (ProductionLog, ProductionLog.date), (Inventory, Inventory.recv_date), (ReceivingChallan, ReceivingChallan.recv_date), (WorkerAdvance, WorkerAdvance.date)):
        for value, in db.session.query(field).all():
            parsed = normalize_date(value)
            if parsed:
                years.add(parsed.year)
    years.update(report.year for report in AnnualReport.query.all())
    return sorted(years, reverse=True)


def annual_report_payload(report_record):
    if not report_record:
        return None
    try:
        return json.loads(report_record.snapshot_json or '{}')
    except (TypeError, ValueError):
        return {}


def owner_only():
    return session.get('role') == 'owner'


def get_active_portal_name():
    portal_key = (session.get('role') or session.get('profile_role') or '').strip()
    portal_labels = {
        'manager': 'Production & Payroll',
        'operations': 'Operations & Logistics',
        'assistant_manager': 'Coordinator',
        'stock': 'Stock',
        'challan': 'Challan',
        'accounts': 'Accounts',
    }
    if portal_key in portal_labels:
        return portal_labels[portal_key]
    return (session.get('name') or session.get('user') or 'System').strip() or 'System'


PORTAL_OPTIONS = [
    ('manager', 'Production & Payroll'),
    ('operations', 'Operations & Logistics'),
    ('assistant_manager', 'Coordinator'),
    ('stock', 'Stock'),
    ('challan', 'Challan'),
    ('accounts', 'Accounts'),
]
PROFILE_ROLE_OPTIONS = [
    ('manager', 'Production & Payroll'),
    ('operations_manager', 'Operations & Logistics'),
    ('assistant_manager', 'Coordinator'),
    ('stock', 'Stock'),
    ('accounts', 'Accounts'),
    ('challan', 'Challan'),
]
PROFILE_ROLE_LABELS = dict(PROFILE_ROLE_OPTIONS)
PROFILE_BASE_PORTAL = {
    'manager': 'manager',
    'operations_manager': 'operations',
    'assistant_manager': 'assistant_manager',
    'stock': 'stock',
    'accounts': 'accounts',
    'challan': 'challan',
}
MANAGER_PORTALS = {'manager', 'stock', 'challan', 'accounts'}
OPERATIONS_MANAGER_PORTALS = {'operations', 'stock', 'challan', 'accounts'}
ASSISTANT_MANAGER_PORTALS = {'assistant_manager', 'stock', 'challan'}
ALL_PORTALS = MANAGER_PORTALS | OPERATIONS_MANAGER_PORTALS | ASSISTANT_MANAGER_PORTALS
PAGE_ACCESS_OPTIONS = [
    ('orders', 'Orders & Articles', ('manager', 'operations', 'assistant_manager')),
    ('receiving_challan', 'Receiving Challan', ('manager', 'operations', 'assistant_manager')),
    ('inventory', 'Inventory', ('manager', 'operations', 'assistant_manager')),
    ('requirements', 'Requirement Slips', ('manager', 'operations', 'assistant_manager')),
    ('order_accessories', 'Order Accessories', ('manager', 'operations', 'assistant_manager')),
    ('cutting', 'Cutting Sheets', ('manager', 'operations', 'assistant_manager')),
    ('production_entry', 'Production Entry', ('manager', 'operations', 'assistant_manager')),
    ('production_log', 'Production Log', ('manager', 'operations', 'assistant_manager')),
    ('summary', 'Master Summary', ('manager', 'operations', 'assistant_manager')),
    ('job_sheet', 'Worker Job Sheets', ('manager', 'operations', 'assistant_manager')),
    ('payout', 'Final Payout', ('manager', 'operations', 'assistant_manager')),
    ('operation_rates', 'Operation Rates', ('manager', 'operations', 'assistant_manager')),
    ('costing', 'Costing Sheets', ('owner',)),
    ('worker_management', 'Worker Management', ('manager', 'operations', 'assistant_manager')),
    ('worker_advance', 'Worker Advance Management', ('manager', 'operations', 'assistant_manager')),
    ('worker_attendance', 'Worker Attendance', ('manager', 'operations', 'assistant_manager')),
    ('vendors', 'Vendors & Items', ('manager', 'operations', 'assistant_manager')),
    ('departments', 'Departments', ('manager', 'operations')),
    ('factory_ledger', 'Factory In/Out Ledger', ('manager', 'operations', 'assistant_manager')),
    ('stock_home', 'Stock Portal', ('stock',)),
    ('fabric', 'Fabric Ledger & Reports', ('stock',)),
    ('accessories', 'Accessories', ('stock',)),
    ('warehouse', 'Warehouse', ('stock',)),
    ('shipments', 'Goods Delivery & Shipments', ('stock',)),
    ('customer_billing', 'Customer Billing', ('accounts',)),
    ('stock_challan', 'Delivery Challan', ('challan',)),
    ('accounts_home', 'Accounts Home', ('accounts',)),
    ('credit_debit', 'Party Credit/Debit', ('accounts',)),
    ('petty_cash', 'Petty Cash', ('accounts',)),
    ('accessories_billing', 'Accessories Billing', ('accounts',)),
    ('utility_bills', 'Utility Bills', ('accounts',)),
    ('utility_bill_summary', 'Utility Bill Summary', ('accounts',)),
]
SPECIAL_ACCESS_OPTIONS = [
    ('fabric_reports', 'Fabric report sections', ('stock',)),
]
PAGE_ACCESS_KEYS = {
    page_key
    for page_key, _, _ in PAGE_ACCESS_OPTIONS + SPECIAL_ACCESS_OPTIONS
}


def portals_allowed_for_role(role):
    if role == 'manager':
        return MANAGER_PORTALS
    if role == 'operations_manager':
        return OPERATIONS_MANAGER_PORTALS
    if role == 'assistant_manager':
        return ASSISTANT_MANAGER_PORTALS
    if role in {'stock', 'accounts', 'challan'}:
        return {'stock', 'accounts', 'challan'}
    return set()


def account_portals(account):
    try:
        configured_portals = json.loads(account.portal_access or '[]')
    except (TypeError, ValueError):
        configured_portals = []
    if not isinstance(configured_portals, list):
        configured_portals = []
    allowed_portals = portals_allowed_for_role(account.role)
    return {portal for portal in configured_portals if portal in allowed_portals}


def pages_allowed_for_portals(portals):
    return {
        page_key
        for page_key, _, page_portals in PAGE_ACCESS_OPTIONS + SPECIAL_ACCESS_OPTIONS
        if set(page_portals) & portals
    }


def account_page_access(account):
    available_pages = pages_allowed_for_portals(account_portals(account))
    try:
        configured_pages = json.loads(account.page_access) if account.page_access else None
    except (TypeError, ValueError):
        configured_pages = None
    if configured_pages is None:
        return available_pages - {'fabric_reports'}
    if not isinstance(configured_pages, list):
        return set()
    configured_page_keys = set(configured_pages)
    if 'workers' in configured_page_keys:
        configured_page_keys.update(('worker_management', 'worker_advance', 'worker_attendance'))
    if 'fabric' not in configured_page_keys:
        configured_page_keys.discard('fabric_reports')
    return {page for page in configured_page_keys if page in available_pages}


def required_page_for_request():
    path = request.path
    if path.startswith('/manager/costing-sheet'):
        return 'costing'
    if path.startswith(('/manager/operation-rates', '/manager/general-operation-rates')):
        return 'operation_rates'
    if path.startswith(('/manager/req-slip', '/manager/saved-requirements')):
        return 'requirements'
    if path.startswith(('/manager/receiving-challan', '/manager/saved-receiving-challans', '/manager/delete-receiving-challan')):
        return 'receiving_challan'
    if path.startswith(('/manager/cutting-sheet', '/manager/saved-cutting-sheets', '/manager/delete-cutting-sheet', '/manager/cutting-transfer')):
        return 'cutting'
    if path.startswith('/manager/bundle-stickers'):
        return 'cutting'
    if path.startswith(('/manager/inventory', '/manager/save-inventory', '/manager/saved-inventory', '/manager/delete-inventory')):
        return 'inventory'
    if path.startswith('/manager/production_entry'):
        return 'production_entry'
    if path.startswith('/manager/production-log'):
        return 'production_log'
    if path.startswith('/manager/summary'):
        return 'summary'
    if path.startswith('/manager/job-sheet'):
        return 'job_sheet'
    if path.startswith(('/manager/payout_sheet', '/payout/')):
        return 'payout'
    if path.startswith('/worker-attendance'):
        return 'worker_attendance'
    if path.startswith('/manager/worker-advance'):
        return 'worker_advance'
    if path.startswith(('/manager/workers', '/manager/worker/', '/manager/delete-worker')):
        return 'worker_management'
    if path.startswith(('/manager/vendors', '/manager/item-list', '/manager/api/item-list', '/manager/api/vendor-items')):
        return 'vendors'
    if path.startswith('/manager/departments'):
        return 'departments'
    if path.startswith('/factory-in-out-ledger'):
        return 'factory_ledger'
    if path.startswith('/manager/article-head'):
        return 'article_head_detail'
    if path.startswith('/order/') and '/accessories' in path:
        return 'order_accessories'
    if path.startswith(('/manager/dashboard', '/manager/articles', '/manager/article/', '/order/')):
        return 'orders'
    if path.startswith(('/accounts/credit-debit-ledger', '/accounts/company-credit-debit')):
        return 'credit_debit'
    if path.startswith('/accounts/petty-cash'):
        return 'petty_cash'
    if path.startswith('/accounts/utility-bill-summary'):
        return 'utility_bill_summary'
    if path.startswith('/accounts/accessories-billing'):
        return 'accessories_billing'
    if path.startswith('/accounts/utility-bills'):
        return 'utility_bills'
    if path == '/accounts':
        return 'accounts_home'
    if path.startswith('/stock-portal/billing'):
        return 'customer_billing'
    if path.startswith('/stock-portal/challan'):
        return 'stock_challan'
    if path.startswith(('/stock-portal/fabric-position-summary', '/stock-portal/article-fabric-and-shipment-summary')):
        return 'fabric_reports'
    if path.startswith('/stock-portal/fabric-ledger'):
        return 'fabric'
    if path.startswith('/stock-portal/accessories'):
        return 'accessories'
    if path.startswith('/stock-portal/warehouse'):
        return 'warehouse'
    if path.startswith(('/stock-portal/goods-delivery', '/stock-portal/orders')):
        return 'shipments'
    if path == '/stock-portal':
        return 'stock_home'
    return None


def required_portal_for_request():
    path = request.path
    if path.startswith('/accounts') or path.startswith('/stock-portal/billing'):
        return 'accounts'
    if path.startswith('/stock-portal/challan'):
        return 'challan'
    if path.startswith('/stock-portal') or path in ('/accounts/accessories-billing', '/accounts/utility-bills'):
        return 'stock'
    if path.startswith('/manager/') or path.startswith('/order/') or path.startswith('/payout/') or path == '/worker-attendance':
        return 'assistant_manager' if session.get('role') == 'assistant_manager' else 'manager'
    return None


@app.before_request
def enforce_profile_portal_access():
    required_portal = required_portal_for_request()
    g.page_access_keys = PAGE_ACCESS_KEYS
    if owner_only() or not session.get('user'):
        return None
    account = PortalAccount.query.filter_by(username=session.get('user')).first()
    profile_role = session.get('profile_role', session.get('role'))
    session_role = 'manager' if profile_role == 'operations_manager' else profile_role
    if account and account.role == profile_role and session.get('role') == session_role:
        allowed_portals = account_portals(account)
        if required_portal is None or required_portal in allowed_portals or (
            profile_role == 'operations_manager'
            and required_portal == 'manager'
            and 'operations' in allowed_portals
        ):
            g.page_access_keys = account_page_access(account)
            required_page = required_page_for_request()
            if required_page is None:
                return None
            if required_page == 'article_head_detail' and 'orders' in g.page_access_keys:
                return None
            if required_page in g.page_access_keys:
                return None
            abort(403)
    elif required_portal is None:
        return None
    flash('Your profile does not have access to this portal.', 'danger')
    return redirect(url_for('index'))


@app.context_processor
def inject_page_access_keys():
    return {
        'page_access_keys': getattr(g, 'page_access_keys', PAGE_ACCESS_KEYS),
        'read_only_profile': is_read_only_profile(),
    }


@app.route('/portal-controls', methods=['GET', 'POST'])
def portal_controls():
    if not owner_only():
        return redirect(url_for('index'))

    accounts = PortalAccount.query.filter(PortalAccount.role != 'owner').order_by(PortalAccount.id).all()
    editing_account = PortalAccount.query.filter_by(
        id=request.args.get('edit_id', type=int)
    ).first() if request.args.get('edit_id') else None
    if request.method == 'POST':
        action = request.form.get('action', 'update')
        account_id = request.form.get('account_id', type=int)
        account = PortalAccount.query.filter_by(id=account_id).first()

        if action == 'delete':
            if not account or account.role == 'owner':
                flash('Portal account not found.', 'danger')
            else:
                db.session.delete(account)
                db.session.commit()
                flash('Portal profile deleted.', 'success')
            return redirect(url_for('portal_controls'))

        username = request.form.get('username', '').strip().lower()
        password = request.form.get('password', '')
        name = request.form.get('name', '').strip()
        role = request.form.get('role', '').strip()
        portal_access = set(request.form.getlist('portal_access')) & portals_allowed_for_role(role)
        base_portal = PROFILE_BASE_PORTAL.get(role)
        if base_portal:
            portal_access.add(base_portal)
        portal_access = sorted(portal_access)
        accessible_pages = pages_allowed_for_portals(set(portal_access))
        page_access = set(request.form.getlist('page_access')) & accessible_pages
        special_access = set(request.form.getlist('special_access')) & accessible_pages
        page_access.update(special_access)
        if 'fabric' not in page_access:
            page_access.discard('fabric_reports')
        page_access = sorted(page_access)

        if action == 'create':
            if role not in PROFILE_BASE_PORTAL:
                flash('Please select a valid portal.', 'danger')
            elif not portal_access:
                flash('Select at least one portal for this profile.', 'danger')
            elif not name or not username or not password:
                flash('Profile name, user ID, and password are required.', 'danger')
            elif PortalAccount.query.filter_by(username=username).first():
                flash('That user ID is already in use.', 'danger')
            else:
                db.session.add(PortalAccount(name=name, username=username, password=password, role=role, portal_access=json.dumps(portal_access), page_access=json.dumps(page_access)))
                db.session.commit()
                flash('Portal profile created.', 'success')
        elif not account or account.role == 'owner':
            flash('Portal account not found.', 'danger')
        elif role not in PROFILE_BASE_PORTAL:
            flash('Please select a valid portal.', 'danger')
        elif not portal_access:
            flash('Select at least one portal for this profile.', 'danger')
        elif not name or not username or not password:
            flash('Profile name, user ID, and password are required.', 'danger')
        elif PortalAccount.query.filter(PortalAccount.username == username, PortalAccount.id != account.id).first():
            flash('That user ID is already in use.', 'danger')
        else:
            account.name = name
            account.username = username
            account.password = password
            account.role = role
            account.portal_access = json.dumps(portal_access)
            account.page_access = json.dumps(page_access)
            db.session.commit()
            flash('Portal profile updated.', 'success')
        return redirect(url_for('portal_controls'))

    account_portal_access = {account.id: account_portals(account) for account in accounts}
    account_page_access_map = {account.id: account_page_access(account) for account in accounts}
    return render_template('portal_controls.html', accounts=accounts, editing_account=editing_account, account_portal_access=account_portal_access, account_page_access=account_page_access_map, portal_options=PORTAL_OPTIONS, page_access_options=PAGE_ACCESS_OPTIONS, special_access_options=SPECIAL_ACCESS_OPTIONS, page_access_keys=PAGE_ACCESS_KEYS, profile_role_options=PROFILE_ROLE_OPTIONS, profile_role_labels=PROFILE_ROLE_LABELS)


@app.route('/annual-reports')
def annual_reports():
    if not owner_only():
        return redirect(url_for('index'))
    reports = AnnualReport.query.order_by(AnnualReport.year.desc()).all()
    return render_template('annual_reports.html', reports=reports, years=annual_report_years())


@app.route('/annual-reports/<int:year>', methods=['GET', 'POST'])
def annual_report(year):
    if not owner_only():
        return redirect(url_for('index'))
    if year < 2000 or year > datetime.now().year + 1:
        flash('Please select a valid reporting year.', 'danger')
        return redirect(url_for('annual_reports'))

    saved_report = AnnualReport.query.filter_by(year=year).first()
    if request.method == 'POST':
        action = request.form.get('action')
        if saved_report and saved_report.status == 'Finalized':
            flash('Finalized annual reports are read-only.', 'danger')
            return redirect(url_for('annual_report', year=year))
        commentary = {field: (request.form.get(field) or '').strip() for field in ('management_message', 'major_achievements', 'major_challenges', 'future_plans', 'additional_notes')}
        if action in ('generate', 'save', 'finalize'):
            snapshot = calculate_annual_report(year)
            if not saved_report:
                saved_report = AnnualReport(year=year, reporting_period=snapshot['reporting_period'], generated_by=session.get('name') or session.get('user'), status='Generated')
                db.session.add(saved_report)
            saved_report.snapshot_json = json.dumps(snapshot)
            saved_report.reporting_period = snapshot['reporting_period']
            saved_report.generated_at = datetime.utcnow()
            saved_report.generated_by = session.get('name') or session.get('user')
            saved_report.management_message = commentary['management_message']
            saved_report.major_achievements = commentary['major_achievements']
            saved_report.major_challenges = commentary['major_challenges']
            saved_report.future_plans = commentary['future_plans']
            saved_report.additional_notes = commentary['additional_notes']
            saved_report.status = 'Finalized' if action == 'finalize' else ('Draft' if action == 'save' else 'Generated')
            if action == 'finalize':
                saved_report.finalized_at = datetime.utcnow()
                saved_report.finalized_by = session.get('name') or session.get('user')
            db.session.commit()
            flash(f'Annual report {year} {saved_report.status.lower()}.', 'success')
        return redirect(url_for('annual_report', year=year))

    payload = annual_report_payload(saved_report) if saved_report else calculate_annual_report(year)
    return render_template('annual_report.html', report=payload, saved_report=saved_report, years=annual_report_years(), now=datetime.now())


@app.route('/annual-reports/<int:year>/print')
def annual_report_print(year):
    if not owner_only():
        return redirect(url_for('index'))
    saved_report = AnnualReport.query.filter_by(year=year).first()
    payload = annual_report_payload(saved_report) if saved_report else calculate_annual_report(year)
    return render_template('annual_report.html', report=payload, saved_report=saved_report, years=[], now=datetime.now(), print_mode=True)


@app.route('/owner-dashboard')
def owner_dashboard():
    if session.get('role') != 'owner':
        return redirect(url_for('index'))

    today = datetime.now()
    month_key = today.strftime('%Y-%m')
    chart_year = today.year
    chart_months = [calendar.month_abbr[month] for month in range(1, 13)]
    orders = Order.query.order_by(Order.id.desc()).all()
    chart_orders_by_job = {order.job_no: order for order in orders if order.job_no}
    logs = ProductionLog.query.order_by(ProductionLog.id.desc()).all()
    cutting_sheets = CuttingSheet.query.order_by(CuttingSheet.id).all()
    workers = Worker.query.order_by(Worker.name).all()
    inventory_records = Inventory.query.order_by(Inventory.id.desc()).all()

    def numeric(value):
        try:
            return float(value or 0)
        except (TypeError, ValueError):
            return 0.0

    def order_quantity(order):
        quantity = numeric(order.new_qty_pcs)
        if not quantity:
            quantity = numeric(order.new_qty_dozen) * 12
        if not quantity:
            quantity = numeric(order.qty)
        return quantity

    monthly_production = [0.0] * 12
    completed_orders = [0] * 12
    dated_logs = []
    for log in logs:
        parsed_log_date = normalize_date(log.date)
        if parsed_log_date and log.job_no:
            dated_logs.append((parsed_log_date, log.id or 0, log))

    final_operation_by_job = {}
    for order in orders:
        operation_names = list(get_rates_for_order(order))
        if order.job_no and operation_names:
            final_operation_by_job[order.job_no] = operation_names[-1].upper()

    production_by_month_and_order = {}
    for parsed_log_date, _, log in dated_logs:
        if (
            parsed_log_date.year != chart_year
            or (log.operation or 'OTHER').upper() != final_operation_by_job.get(log.job_no)
        ):
            continue
        month_index = parsed_log_date.month - 1
        order_totals = production_by_month_and_order.setdefault(month_index, {})
        order_totals[log.job_no] = order_totals.get(log.job_no, 0) + (log.pcs or 0)
    for month_index, order_totals in production_by_month_and_order.items():
        monthly_production[month_index] = sum(order_totals.values())

    cumulative_by_order = {}
    completed_job_numbers = set()
    for parsed_log_date, _, log in sorted(dated_logs, key=lambda item: (item[0], item[1])):
        if (log.operation or 'OTHER').upper() != final_operation_by_job.get(log.job_no):
            continue
        cumulative_by_order[log.job_no] = cumulative_by_order.get(log.job_no, 0) + (log.pcs or 0)
        order_record = chart_orders_by_job.get(log.job_no)
        order_total = order_quantity(order_record) if order_record else 0
        produced_pcs = cumulative_by_order[log.job_no]
        if order_total > 0 and produced_pcs >= order_total and log.job_no not in completed_job_numbers:
            if parsed_log_date.year == chart_year:
                completed_orders[parsed_log_date.month - 1] += 1
            completed_job_numbers.add(log.job_no)

    month_logs = [log for log in logs if str(log.date or '').startswith(month_key)]
    labor_cost = sum((log.pcs or 0) * get_rate_for_log(log) for log in month_logs)
    all_labor_cost = sum((log.pcs or 0) * get_rate_for_log(log) for log in logs)
    production_pcs = sum(
        (log.pcs or 0)
        for log in month_logs
        if (log.operation or 'OTHER').upper() == final_operation_by_job.get(log.job_no)
    )
    all_production_pcs = sum(
        get_order_shipping_snapshot(order)['completed_pcs']
        for order in orders
    )
    inventory_quantity = sum(numeric(record.quantity) for record in inventory_records)
    inventory_received = sum(numeric(record.fabric_qty_a) + numeric(record.fabric_qty_b) for record in inventory_records)
    fabric_received = sum(numeric(record.fabric_qty_a) + numeric(record.fabric_qty_b) for record in inventory_records)
    fabric_used = sum(numeric(sheet.total_meter) for sheet in cutting_sheets)
    fabric_left = max(0.0, fabric_received - fabric_used)
    outstanding_advances = sum(get_worker_advance_summary(worker.name)[0] for worker in workers if worker.name)
    workers_with_advances = sum(1 for worker in workers if worker.name and get_worker_advance_summary(worker.name)[0] > 0)

    def is_current_month(date_value):
        parsed = normalize_date(date_value)
        return bool(parsed and parsed.strftime('%Y-%m') == month_key)

    billing_invoices = BillingInvoice.query.all()
    customer_bills = CustomerBill.query.all()
    invoice_challan_ids = {invoice.challan_id for invoice in billing_invoices}
    invoice_challan_ids.update(
        challan_id for (challan_id,) in BillingInvoiceChallan.query.with_entities(
            BillingInvoiceChallan.challan_id
        ).all()
    )
    customer_bill_challans = {bill.id: {bill.challan_id} for bill in customer_bills}
    for bill_id, challan_id in CustomerBillChallan.query.with_entities(
        CustomerBillChallan.bill_id,
        CustomerBillChallan.challan_id,
    ).all():
        customer_bill_challans.setdefault(bill_id, set()).add(challan_id)
    standalone_customer_bills = [
        bill for bill in customer_bills
        if not customer_bill_challans.get(bill.id, set()).intersection(invoice_challan_ids)
    ]
    monthly_sales_invoiced = sum(
        numeric(invoice.total)
        for invoice in billing_invoices
        if is_current_month(invoice.invoice_date)
    ) + sum(
        numeric(bill.total)
        for bill in standalone_customer_bills
        if is_current_month(bill.invoice_date)
    )
    monthly_customer_receipts = sum(
        numeric(payment.amount)
        for invoice in billing_invoices
        for payment in invoice.payments
        if is_current_month(payment.paid_on)
    ) + sum(
        numeric(payment.amount)
        for bill in standalone_customer_bills
        for payment in bill.payments
        if is_current_month(payment.paid_on)
    )
    accounts_receivable = sum(
        max(0.0, numeric(invoice.total) - sum(numeric(payment.amount) for payment in invoice.payments))
        for invoice in billing_invoices
    ) + sum(
        max(0.0, numeric(bill.total) - sum(numeric(payment.amount) for payment in bill.payments))
        for bill in standalone_customer_bills
    )
    utility_bills = UtilityBill.query.all()
    monthly_utility_bills = sum(
        numeric(bill.amount)
        for bill in utility_bills
        if bill.billing_period == month_key
    )
    utility_outstanding = sum(
        max(0.0, numeric(bill.amount) - sum(numeric(payment.amount) for payment in bill.payments))
        for bill in utility_bills
    )
    monthly_accessory_bills = sum(
        numeric(requirement.bill_amount)
        for requirement in SavedRequirement.query.all()
        if is_current_month(requirement.date) and numeric(requirement.bill_amount) > 0
    )
    manual_entries = ManualCreditDebitEntry.query.all()
    monthly_manual_credits = sum(
        numeric(entry.amount)
        for entry in manual_entries
        if entry.direction.upper() == 'CREDIT' and is_current_month(entry.date)
    )
    monthly_manual_debits = sum(
        numeric(entry.amount)
        for entry in manual_entries
        if entry.direction.upper() == 'DEBIT' and is_current_month(entry.date)
    )
    billed_challan_ids = set(invoice_challan_ids)
    for challan_ids in customer_bill_challans.values():
        billed_challan_ids.update(challan_ids)
    unbilled_challan_count = sum(
        1 for challan in ChallanRecord.query.filter_by(source_type='order').all()
        if challan.id not in billed_challan_ids
    )
    active_worker_names = {log.worker for log in month_logs if log.worker}
    production_by_operation = {}
    for log in month_logs:
        operation = (log.operation or 'OTHER').upper()
        production_by_operation[operation] = production_by_operation.get(operation, 0) + (log.pcs or 0)
    top_operations = sorted(production_by_operation.items(), key=lambda item: item[1], reverse=True)[:5]
    max_operation_pcs = max((value for _, value in top_operations), default=1)

    orders_by_job = {order.job_no: order for order in orders if order.job_no}
    cuts_by_order = {}
    sheets_by_order = {}
    for sheet in cutting_sheets:
        cuts_by_order.setdefault(str(sheet.order_id), set()).add(str(sheet.id))
        sheets_by_order.setdefault(str(sheet.order_id), []).append(sheet)
    inventory_by_order = {}
    for record in inventory_records:
        inventory_by_order[str(record.order_id)] = inventory_by_order.get(str(record.order_id), 0.0) + numeric(record.fabric_qty_a) + numeric(record.fabric_qty_b)
    article_key_by_job = {}
    for order in orders:
        if not order.job_no:
            continue
        if order.article_id:
            article_key = ('id', order.article_id)
        else:
            article_name = (order.article_name or '').strip().casefold()
            article_code = (order.article or '').strip().casefold()
            article_key = ('name', article_name) if article_name else ('code', article_code)
        article_key_by_job[str(order.job_no)] = article_key
    inventory_by_article = {}
    for job_no, article_key in article_key_by_job.items():
        inventory_by_article[article_key] = inventory_by_article.get(article_key, 0.0) + inventory_by_order.get(job_no, 0.0)
    monthly_order_logs = {}
    for log in month_logs:
        if log.job_no:
            monthly_order_logs.setdefault(log.job_no, []).append(log)
    all_order_logs = {}
    for log in logs:
        if log.job_no:
            all_order_logs.setdefault(str(log.job_no), []).append(log)
    order_summaries = []
    for job_no, order_logs in monthly_order_logs.items():
        order_record = orders_by_job.get(job_no)
        order_pcs_total = order_quantity(order_record) if order_record else 0
        operation_totals = {}
        for log in order_logs:
            operation = (log.operation or 'OTHER').upper()
            operation_totals[operation] = operation_totals.get(operation, 0) + (log.pcs or 0)
        order_sheets = sheets_by_order.get(str(job_no), [])
        operation_names = list(dict.fromkeys(
            operation
            for sheet in order_sheets
            for operation in get_rates_for_cut(order_record, sheet.cut_no)
        )) if order_record else []
        if not operation_names:
            operation_names = list(operation_totals)
        operation_logs = all_order_logs.get(str(job_no), [])
        stitched_operations = {
            (rate.operation or '').upper()
            for rate in OperationRate.query.filter(
                func.upper(OperationRate.operation).in_(operation_names)
            ).all()
            if rate.is_stitched_operation
        } if operation_names else set()
        operation_progress = {
            operation: {'completed_pcs': 0.0, 'required_pcs': 0.0, 'completed_cuts': 0, 'total_cuts': 0}
            for operation in operation_names
        }
        total_operation_pcs = 0.0
        completed_operation_pcs = 0.0
        completed_operation_cuts = 0
        total_operation_cuts = 0
        if order_sheets and operation_names:
            for sheet in order_sheets:
                cut_operation_names = list(get_rates_for_cut(order_record, sheet.cut_no))
                if not cut_operation_names:
                    continue
                cut_logs = [
                    log for log in operation_logs
                    if str(log.cut_no) == str(sheet.cut_no)
                ]
                state = get_cut_production_state(
                    job_no,
                    sheet.cut_no,
                    numeric(sheet.quantity),
                    cut_operation_names,
                    logs=cut_logs,
                )
                for operation in cut_operation_names:
                    total = state['raw_totals'].get(operation, 0)
                    limit = state['effective_limits'].get(
                        operation,
                        state['limits_before_bq'].get(operation, numeric(sheet.quantity)),
                    ) if state['machine_operations'].get(operation) else state['limits_before_bq'].get(operation, numeric(sheet.quantity))
                    if operation in stitched_operations:
                        total += state['stitched_bq_totals'].get(operation, 0)
                        limit = state['limits_before_bq'].get(operation, numeric(sheet.quantity))
                    limit = max(0.0, float(limit))
                    total = max(0.0, float(total))
                    progress = operation_progress[operation]
                    progress['completed_pcs'] += min(total, limit)
                    progress['required_pcs'] += limit
                    progress['total_cuts'] += 1
                    total_operation_pcs += limit
                    completed_operation_pcs += min(total, limit)
                    total_operation_cuts += 1
                    if total >= limit:
                        progress['completed_cuts'] += 1
                        completed_operation_cuts += 1
        else:
            fallback_required = order_pcs_total or max(operation_totals.values(), default=0)
            for operation in operation_names:
                total = sum(
                    numeric(log.pcs)
                    + (numeric(log.bq_stitched) if operation in stitched_operations else 0)
                    for log in operation_logs
                    if (log.operation or '').upper() == operation
                )
                progress = operation_progress[operation]
                progress['completed_pcs'] = min(total, fallback_required)
                progress['required_pcs'] = fallback_required
                progress['total_cuts'] = 1 if fallback_required > 0 else 0
                progress['completed_cuts'] = int(fallback_required > 0 and total >= fallback_required)
                total_operation_pcs += fallback_required
                completed_operation_pcs += min(total, fallback_required)
                total_operation_cuts += progress['total_cuts']
                completed_operation_cuts += progress['completed_cuts']
        order_operations = [
            {
                'operation': operation,
                **progress,
                'percentage': round(
                    min(100.0, progress['completed_pcs'] / progress['required_pcs'] * 100)
                    if progress['required_pcs'] else 0.0,
                    1,
                ),
            }
            for operation, progress in operation_progress.items()
        ]
        overall_operation_completion = round(
            min(100.0, completed_operation_pcs / total_operation_pcs * 100)
            if total_operation_pcs else 0.0,
            1,
        )
        order_shipping = get_order_shipping_snapshot(order_record) if order_record else {}
        order_pcs = order_shipping.get(
            'completed_pcs', max(operation_totals.values(), default=0)
        )
        shipped_pcs = order_shipping.get('shipped_pcs', 0)
        excess_pcs = max(0, shipped_pcs - order_pcs_total)
        is_completed = order_pcs_total > 0 and shipped_pcs >= order_pcs_total
        is_ready_to_ship = (
            not is_completed and order_pcs_total > 0 and order_pcs >= order_pcs_total
        )
        order_cost = sum((log.pcs or 0) * get_rate_for_log(log) for log in order_logs)
        article_key = article_key_by_job.get(str(job_no))
        order_fabric_received = (
            inventory_by_article.get(article_key, 0.0)
            if article_key else inventory_by_order.get(str(job_no), 0.0)
        )
        order_fabric_used = sum(
            numeric(sheet.total_meter)
            for sheet in cutting_sheets
            if str(sheet.order_id) == str(job_no)
        )
        order_summaries.append({
            'job_no': job_no,
            'party': (order_record.name if order_record else None) or order_logs[0].party or '-',
            'article': (order_record.article_name if order_record else None) or order_logs[0].article_name or order_logs[0].article or '-',
            'color': (order_record.color if order_record else None) or order_logs[0].color or '-',
            'order_pcs': round(order_pcs_total, 2),
            'pieces': order_pcs,
            'shipped_pcs': shipped_pcs,
            'excess_pcs': excess_pcs,
            'is_completed': is_completed,
            'is_ready_to_ship': is_ready_to_ship,
            'remaining_pcs': max(0, round(order_pcs_total - order_pcs, 2)),
            'labor_cost': round(order_cost, 2),
            'cuts': len(cuts_by_order.get(str(job_no), set())),
            'fabric_received': round(order_fabric_received, 2),
            'fabric_used': round(order_fabric_used, 2),
            'fabric_left': round(max(0.0, order_fabric_received - order_fabric_used), 2),
            'operations': order_operations,
            'overall_operation_completion': overall_operation_completion,
            'completed_operation_cuts': completed_operation_cuts,
            'total_operation_cuts': total_operation_cuts,
            'recent_logs': sorted(order_logs, key=lambda log: log.id or 0, reverse=True)[:5],
        })
    order_summaries.sort(key=lambda item: item['pieces'], reverse=True)

    order_job_numbers = {order.job_no for order in orders if order.job_no}
    logged_job_numbers = {log.job_no for log in logs if log.job_no}
    pending_orders = sum(1 for job_no in order_job_numbers if job_no not in logged_job_numbers)
    recent_activity = logs[:8]
    current_annual_report = AnnualReport.query.filter_by(year=today.year).first()
    annual_dashboard_payload = annual_report_payload(current_annual_report) if current_annual_report else calculate_annual_report(today.year, include_comparison=False)
    annual_dashboard_kpis = annual_dashboard_payload.get('kpis', {})

    return render_template(
        'owner_dashboard.html',
        month_label=today.strftime('%B %Y'),
        chart_year=chart_year,
        chart_months=chart_months,
        chart_completed_orders=completed_orders,
        chart_monthly_production=[round(value, 2) for value in monthly_production],
        orders_count=len(orders),
        articles_count=Article.query.count(),
        workers_count=len(workers),
        inventory_count=len(inventory_records),
        production_pcs=production_pcs,
        all_production_pcs=all_production_pcs,
        labor_cost=round(labor_cost, 2),
        all_labor_cost=round(all_labor_cost, 2),
            monthly_sales_invoiced=round(monthly_sales_invoiced, 2),
            monthly_customer_receipts=round(monthly_customer_receipts, 2),
            accounts_receivable=round(accounts_receivable, 2),
            monthly_utility_bills=round(monthly_utility_bills, 2),
            utility_outstanding=round(utility_outstanding, 2),
            monthly_accessory_bills=round(monthly_accessory_bills, 2),
            monthly_manual_credits=round(monthly_manual_credits, 2),
            monthly_manual_debits=round(monthly_manual_debits, 2),
            unbilled_challan_count=unbilled_challan_count,
        inventory_quantity=round(inventory_quantity, 2),
        inventory_received=round(inventory_received, 2),
        fabric_received=round(fabric_received, 2),
        fabric_used=round(fabric_used, 2),
        fabric_left=round(fabric_left, 2),
        outstanding_advances=round(outstanding_advances, 2),
        active_worker_count=len(active_worker_names),
        workers_with_advances=workers_with_advances,
        pending_orders=pending_orders,
        top_operations=top_operations,
        max_operation_pcs=max_operation_pcs,
        recent_activity=recent_activity,
        order_summaries=order_summaries,
        annual_report_year=today.year,
        annual_report_year_options=annual_report_years(),
        annual_report_status=current_annual_report.status if current_annual_report else 'Not Generated',
        annual_report_generated_at=current_annual_report.generated_at if current_annual_report else None,
        annual_report_finalized_at=current_annual_report.finalized_at if current_annual_report else None,
        annual_report_kpis=annual_dashboard_kpis,
    )

@app.route('/worker-dashboard')
def worker_dashboard():
    if session.get('role') != 'worker' or not session.get('worker_id'):
        return redirect(url_for('index'))

    worker = Worker.query.get(session['worker_id'])
    if not worker:
        session.clear()
        flash('Worker account could not be found.', 'danger')
        return redirect(url_for('index'))

    today = datetime.now()
    try:
        selected_year = int(request.args.get('year', today.year))
        selected_month = int(request.args.get('month', today.month))
        if selected_month not in range(1, 13):
            raise ValueError
    except (TypeError, ValueError):
        selected_year, selected_month = today.year, today.month

    month_prefix = f'{selected_year:04d}-{selected_month:02d}'
    worker_logs = ProductionLog.query.filter(
        func.lower(ProductionLog.worker) == (worker.name or '').strip().lower()
    ).order_by(ProductionLog.id.desc()).all()
    month_logs = [log for log in worker_logs if str(log.date or '').startswith(month_prefix)]

    def numeric(value):
        try:
            return float(value or 0)
        except (TypeError, ValueError):
            return 0.0

    daily_map = {}
    operation_map = {}
    total_earnings = 0.0
    for log in month_logs:
        pieces = numeric(log.pcs)
        rate = get_rate_for_log(log)
        earnings = pieces * rate
        date_key = str(log.date or 'Unknown')
        day = daily_map.setdefault(date_key, {'date': date_key, 'pieces': 0, 'earnings': 0.0, 'entries': 0})
        day['pieces'] += pieces
        day['earnings'] += earnings
        day['entries'] += 1
        operation = (log.operation or 'OTHER').upper()
        summary = operation_map.setdefault(operation, {'operation': operation, 'pieces': 0, 'rate': rate, 'earnings': 0.0})
        summary['pieces'] += pieces
        summary['earnings'] += earnings
        total_earnings += earnings

    attendance = Attendance.query.filter_by(worker_id=worker.id, year=selected_year, month=selected_month).first()
    advance_entries = WorkerAdvance.query.filter_by(worker_id=worker.id).order_by(WorkerAdvance.date.desc(), WorkerAdvance.id.desc()).all()
    month_advances = [entry for entry in advance_entries if str(entry.date or '').startswith(month_prefix)]
    total_advances = sum(numeric(entry.amount) for entry in advance_entries if entry.record_type == 'advance')
    total_payments = sum(numeric(entry.amount) for entry in advance_entries if entry.record_type == 'payment')
    month_advance_total = sum(numeric(entry.amount) for entry in month_advances if entry.record_type == 'advance')
    month_payment_total = sum(numeric(entry.amount) for entry in month_advances if entry.record_type == 'payment')

    return render_template(
        'worker_dashboard.html',
        worker=worker,
        selected_year=selected_year,
        selected_month=selected_month,
        month_label=datetime(selected_year, selected_month, 1).strftime('%B %Y'),
        month_options=[(number, calendar.month_name[number]) for number in range(1, 13)],
        rate_for_operation_at=get_rate_for_operation_at,
        month_logs=month_logs,
        daily_progress=sorted(daily_map.values(), key=lambda item: item['date'], reverse=True),
        operation_summary=sorted(operation_map.values(), key=lambda item: item['earnings'], reverse=True),
        total_pieces=sum(numeric(log.pcs) for log in month_logs),
        total_earnings=total_earnings,
        attendance=attendance,
        advance_entries=advance_entries,
        month_advances=month_advances,
        total_advances=total_advances,
        total_payments=total_payments,
        outstanding_advances=max(0.0, total_advances - total_payments),
        month_advance_total=month_advance_total,
        month_payment_total=month_payment_total,
        net_payable=total_earnings - month_advance_total + month_payment_total,
    )



def generate_po_no():
    # Get the last SavedRequirement id only (avoid selecting missing columns)
    last_req_row = db.session.query(SavedRequirement.id).order_by(SavedRequirement.id.desc()).first()
    last_id = last_req_row[0] if last_req_row else None
    next_po = last_id + 1 if last_id else 1
    return f"{next_po:03d}"


def generate_cutting_sheet_serial():
    try:
        year = datetime.now().strftime('%Y')
        candidates = []
        rows = CuttingSheet.query.filter(CuttingSheet.serial_no.like(f'%/{year}')).all()
        for row in rows:
            match = re.fullmatch(rf'\s*(\d+)\s*/\s*{re.escape(year)}\s*', row.serial_no or '')
            if match:
                candidates.append(int(match.group(1)))

        first_serial_number = 312 if year == '2026' else 1
        next_number = max(max(candidates, default=0) + 1, first_serial_number)
        return f'{next_number:03d}/{year}'
    except Exception:
        year = datetime.now().strftime('%Y')
        return f"{'312' if year == '2026' else '001'}/{year}"


def get_next_cut_no_for_order(job_no):
    try:
        sheets = CuttingSheet.query.filter_by(order_id=job_no).all()
        max_cut = 0
        for sheet in sheets:
            try:
                cut_value = int(sheet.cut_no) if sheet.cut_no is not None else 0
            except (ValueError, TypeError):
                continue
            max_cut = max(max_cut, cut_value)
        return str(max_cut + 1)
    except Exception:
        return "1"


@app.route('/manager/req-slip', methods=['GET', 'POST'])
def req_slip():
    if not session.get('role'):
        return redirect(url_for('index'))

    job_no = request.args.get('job_no') or request.args.get('order_id') or request.args.get('auto_job')
    req_id = request.args.get('req_id') or request.form.get('req_id')
    po_no_param = request.args.get('po_no') or request.form.get('po_no')
    order = Order.query.filter_by(job_no=job_no).first() if job_no else None
    vendors = Vendor.query.order_by(Vendor.name.asc()).all()
    item_master_data = [
        {
            'item_name': item.item_name,
            'material': item.material or '',
            'size': item.size or '',
            'unit': item.unit or '',
            'issue_unit': item.issue_unit or item.unit or '',
            'issue_unit_factor': float(item.issue_unit_factor or 1.0),
        }
        for item in ItemMaster.query.order_by(ItemMaster.item_name.asc()).all()
    ]
    item_master_by_name = {
        item['item_name'].strip().casefold(): item
        for item in item_master_data
        if item['item_name']
    }
    auto_calculate_rolls = bool(order and not req_id and not po_no_param)
    article_specs = ArticleMaterialSpec.query.filter_by(article_id=order.article_id).order_by(
        ArticleMaterialSpec.sort_order.asc(), ArticleMaterialSpec.id.asc()
    ).all() if order and order.article_id else []
    article_usage_data = [
        {'item_name': spec.item_name or '', 'qty_per_piece': parse_numeric(spec.qty_per_piece), 'unit': spec.unit or ''}
        for spec in article_specs
    ]
    order_requirement_qty = get_effective_order_quantity(order) if order else 0.0

    edit_req = None
    prefill = {
        'item_1': '', 'item_2': '', 'item_3': '', 'item_4': '', 'item_5': '', 'item_6': '',
        'qty_1': '', 'qty_2': '', 'qty_3': '', 'qty_4': '', 'qty_5': '', 'qty_6': '',
        'size_1': '', 'size_2': '', 'size_3': '', 'size_4': '', 'size_5': '', 'size_6': '',
        'unit_1': '', 'unit_2': '', 'unit_3': '', 'unit_4': '', 'unit_5': '', 'unit_6': '',
        'quality_1': '', 'quality_2': '', 'quality_3': '', 'quality_4': '', 'quality_5': '', 'quality_6': '',
        'rate_1': '', 'rate_2': '', 'rate_3': '', 'rate_4': '', 'rate_5': '', 'rate_6': '',
        'bill_amount_1': '', 'bill_amount_2': '', 'bill_amount_3': '', 'bill_amount_4': '', 'bill_amount_5': '', 'bill_amount_6': '',
        'requested_by': '',
        'priority': '',
        'supplier': '',
        'date': '',
        'for_field': '',
        'po_no': generate_po_no(),
        'serial_no': generate_requirement_serial()
    }

    # If PO number provided, load all SavedRequirement rows for that PO and populate multiple item slots
    if po_no_param:
        po_clean = po_no_param.strip()
        po_rows = SavedRequirement.query.filter_by(order_id=job_no, po_no=po_clean).order_by(SavedRequirement.id.asc()).all() if job_no else []
        idx = 1
        for r in po_rows:
            if idx > 6:
                break
            prefill[f'item_{idx}'] = r.item or ''
            prefill[f'qty_{idx}'] = r.qty or ''
            prefill[f'size_{idx}'] = r.size or ''
            prefill[f'unit_{idx}'] = r.unit or ''
            prefill[f'quality_{idx}'] = r.quality or ''
            prefill[f'rate_{idx}'] = r.rate or ''
            prefill[f'bill_amount_{idx}'] = r.bill_amount or ''
            idx += 1
        # set header fields, po_no and serial from first row if present
        if po_rows:
            first = po_rows[0]
            prefill['requested_by'] = first.requested_by or prefill['requested_by']
            prefill['priority'] = first.priority or prefill['priority']
            prefill['supplier'] = first.supplier or prefill['supplier']
            prefill['date'] = first.date or prefill['date']
            prefill['for_field'] = first.for_field or prefill['for_field']
            prefill['po_no'] = first.po_no or prefill['po_no']
            prefill['serial_no'] = first.serial_no or prefill['serial_no']

    if order and not req_id and not po_no_param:
        existing_req_count = SavedRequirement.query.filter_by(order_id=job_no).count()
        if existing_req_count == 0:
            if article_specs:
                prefill['supplier'] = find_lowest_cost_vendor(article_specs, order_requirement_qty)
                for idx, spec in enumerate(article_specs[:6], start=1):
                    qty_value = ''
                    try:
                        order_qty = order_requirement_qty
                        spec_qty = float(spec.qty_per_piece or 0)
                        if order_qty and spec_qty:
                            master_item = item_master_by_name.get((spec.item_name or '').strip().casefold())
                            if length_to_meters(1, spec.unit) > 0:
                                qty_value = str(length_to_meters(order_qty * spec_qty, spec.unit))
                            elif master_item and is_package_unit(master_item['unit']):
                                vendor = Vendor.query.filter(func.lower(Vendor.name) == prefill['supplier'].lower()).first()
                                vendor_item = next((
                                    candidate for candidate in (vendor.items if vendor else [])
                                    if (candidate.item_name or '').strip().casefold() == (spec.item_name or '').strip().casefold()
                                ), None)
                                units_per_package = parse_numeric(vendor_item.pack_qty) if vendor_item and is_package_unit(vendor_item.unit) else 0.0
                                if vendor_item and (spec.unit or '').strip().casefold() == (vendor_item.unit or '').strip().casefold():
                                    qty_value = str(order_qty * spec_qty)
                                elif units_per_package > 0:
                                    package_qty = math.ceil(order_qty * spec_qty / units_per_package - 1e-10)
                                    qty_value = str(package_qty) if package_qty else ''
                                elif (spec.unit or '').strip().casefold() == (master_item['unit'] or '').strip().casefold():
                                    qty_value = str(order_qty * spec_qty)
                            elif master_item and is_roll_unit(master_item['unit']):
                                vendor = Vendor.query.filter(func.lower(Vendor.name) == prefill['supplier'].lower()).first()
                                vendor_item = next((
                                    candidate for candidate in (vendor.items if vendor else [])
                                    if (candidate.item_name or '').strip().casefold() == (spec.item_name or '').strip().casefold()
                                ), None)
                                roll_qty = required_roll_quantity(
                                    order_qty, spec_qty, spec.unit, vendor_item.pack_qty if vendor_item else 0
                                )
                                qty_value = str(roll_qty) if roll_qty else ''
                            else:
                                qty_value = str(round(order_qty * spec_qty))
                    except (TypeError, ValueError):
                        qty_value = ''

                    prefill[f'item_{idx}'] = spec.item_name or ''
                    prefill[f'qty_{idx}'] = qty_value
                    master_item = item_master_by_name.get((spec.item_name or '').strip().casefold())
                    prefill[f'size_{idx}'] = spec.size or (master_item['size'] if master_item else '') or ''
                    prefill[f'unit_{idx}'] = (
                        'METER' if length_to_meters(1, spec.unit) > 0
                        else (
                            master_item['unit']
                            if master_item and (
                                is_package_unit(master_item['unit'])
                                or is_roll_unit(master_item['unit'])
                            )
                            else spec.unit or (master_item['unit'] if master_item else '') or ''
                        )
                    )
                    prefill[f'quality_{idx}'] = spec.material or (master_item['material'] if master_item else '') or ''
                    prefill[f'rate_{idx}'] = ''
                    prefill[f'bill_amount_{idx}'] = ''

    if req_id:
        edit_req = SavedRequirement.query.get(req_id)
        if edit_req:
            prefill['item_1'] = edit_req.item or ''
            prefill['qty_1'] = edit_req.qty or ''
            prefill['size_1'] = edit_req.size or ''
            prefill['unit_1'] = edit_req.unit or ''
            prefill['quality_1'] = edit_req.quality or ''
            prefill['rate_1'] = edit_req.rate or ''
            prefill['bill_amount_1'] = edit_req.bill_amount or ''
            prefill['requested_by'] = edit_req.requested_by or ''
            prefill['priority'] = edit_req.priority or ''
            prefill['supplier'] = edit_req.supplier or ''
            prefill['date'] = edit_req.date or ''
            prefill['for_field'] = edit_req.for_field or ''
            prefill['po_no'] = edit_req.po_no or prefill['po_no']
            prefill['serial_no'] = edit_req.serial_no or prefill['serial_no']

    if request.method == 'POST':
        date = request.form.get('date')
        requested_by = request.form.get('requested_by')
        supplier = request.form.get('supplier')
        priority = request.form.get('priority')
        serial_no = request.form.get('serial_no') or generate_requirement_serial()
        for_field = request.form.get('for_field')
        po_no = request.form.get('po_no')  # will come from hidden field
        req_id = request.form.get('req_id')
        existing_po = bool(
            po_no and SavedRequirement.query.filter_by(order_id=job_no, po_no=po_no).first()
        )
        auto_calculate_rolls = bool(order and not req_id and not existing_po)

        if req_id and is_read_only_profile():
            return reject_read_only_edit()
        if is_read_only_profile() and po_no and SavedRequirement.query.filter_by(order_id=job_no, po_no=po_no).first():
            return reject_read_only_edit()

        # If saving by P.O. (po_no present) and not editing a single saved row (no req_id),
        # replace all existing SavedRequirement rows for this order+po_no with the submitted rows.
        if po_no and not req_id:
            try:
                SavedRequirement.query.filter_by(order_id=job_no, po_no=po_no).delete()
                db.session.flush()
            except Exception:
                db.session.rollback()

        saved = False
        if req_id:
            edit_req = SavedRequirement.query.get(req_id)

        for i in range(1, 7):
            item = request.form.get(f'item_{i}', '').strip()
            qty = request.form.get(f'qty_{i}', '').strip()
            size = request.form.get(f'size_{i}', '').strip()
            unit = request.form.get(f'unit_{i}', '').strip()
            quality = request.form.get(f'quality_{i}', '').strip()
            rate = request.form.get(f'rate_{i}', '').strip()
            bill_amount = request.form.get(f'bill_amount_{i}', '').strip()
            master_item = item_master_by_name.get(item.casefold())
            roll_length_m = 0.0
            if is_roll_unit(unit):
                vendor = Vendor.query.filter(func.lower(Vendor.name) == (supplier or '').strip().lower()).first()
                vendor_item = next((
                    candidate for candidate in (vendor.items if vendor else [])
                    if (candidate.item_name or '').strip().casefold() == item.casefold()
                ), None)
                roll_length_m = parse_numeric(vendor_item.pack_qty) if vendor_item and is_roll_unit(vendor_item.unit) else 0.0
                if roll_length_m <= 0:
                    flash(f'Enter meters per roll for {item} in the selected vendor record.', 'danger')
                    return redirect(url_for('req_slip', job_no=job_no))
                try:
                    if float(qty) != float(int(float(qty))):
                        raise ValueError
                    qty = str(int(float(qty)))
                except (TypeError, ValueError):
                    flash(f'{item} must be requested as a whole number of rolls.', 'danger')
                    return redirect(url_for('req_slip', job_no=job_no))
                if auto_calculate_rolls:
                    spec = next((
                        row for row in article_specs
                        if (row.item_name or '').strip().casefold() == item.casefold()
                    ), None)
                    if spec:
                        qty = str(required_roll_quantity(
                            order_requirement_qty, parse_numeric(spec.qty_per_piece), spec.unit, roll_length_m
                        ))
                        rate = f'{parse_numeric(vendor_item.pack_price):.2f}'
                        bill_amount = f'{parse_numeric(qty) * parse_numeric(rate):.2f}'

            if qty and rate:
                bill_amount = f'{parse_numeric(qty) * parse_numeric(rate):.2f}'

            if i == 1 and req_id and edit_req:
                if item or qty or size or unit or quality:
                    edit_req.item = item
                    edit_req.qty = qty
                    edit_req.size = size
                    edit_req.unit = unit
                    edit_req.roll_length_m = roll_length_m or edit_req.roll_length_m
                    edit_req.quality = quality
                    edit_req.rate = rate
                    edit_req.bill_amount = bill_amount
                    edit_req.serial_no = serial_no
                    edit_req.requested_by = requested_by
                    edit_req.priority = priority
                    edit_req.date = date
                    edit_req.for_field = for_field
                    edit_req.po_no = po_no
                    edit_req.supplier = supplier
                    saved = True
                    continue

            if item or qty or size or unit or quality:
                default_issue_unit = unit
                default_issue_factor = 1.0
                master_item = item_master_by_name.get(item.casefold())
                if master_item:
                    default_issue_unit = (master_item.get('issue_unit') or master_item.get('unit') or unit).strip() or unit
                    default_issue_factor = float(master_item.get('issue_unit_factor') or 1.0)
                saved_req = SavedRequirement(
                    order_id=job_no,
                    item=item,
                    qty=qty,
                    size=size,
                    unit=unit,
                    roll_length_m=roll_length_m,
                    issue_unit=default_issue_unit,
                    issue_unit_factor=default_issue_factor,
                    quality=quality,
                    rate=rate,
                    bill_amount=bill_amount,
                    supplier=supplier,
                    serial_no=serial_no,
                    requested_by=requested_by,
                    priority=priority,
                    date=date,
                    for_field=for_field,
                    po_no=po_no
                )
                db.session.add(saved_req)
                saved = True

        if saved:
            if po_no and not req_id:
                po_requirements = SavedRequirement.query.filter_by(order_id=job_no, po_no=po_no).all()
                sent_date = datetime.utcnow().strftime('%Y-%m-%d')
                for po_requirement in po_requirements:
                    po_requirement.accessory_status = 'PO_SENT'
                    po_requirement.po_sent_at = sent_date
            db.session.commit()
            flash('Requirement saved successfully.' if not req_id else 'Requirement updated successfully.', 'success')
        else:
            flash('Please enter at least one item before saving.', 'danger')

        return redirect(url_for('saved_requirements', order_id=job_no))

    return render_template(
        'req_slip.html',
        order_id=job_no,
        selected_job=job_no,
        order=order,
        hide_logo=True,
        serial_no=prefill['serial_no'],
        po_no=prefill['po_no'],
        req_id=req_id,
        prefill=prefill,
        vendors=vendors,
        item_master_data=item_master_data,
        article_usage_data=article_usage_data,
        order_requirement_qty=order_requirement_qty,
        auto_calculate_rolls=auto_calculate_rolls,
    )


def generate_inventory_serial():
    return get_next_serial()


def generate_requirement_serial():
    return get_next_serial()


def normalize_challan_number(value):
    if value is None:
        return ''
    cleaned = str(value).strip()
    if not cleaned:
        return ''
    cleaned = cleaned.replace('CH-', '', 1).replace('ch-', '', 1)
    cleaned = cleaned.replace('C-', '', 1).replace('c-', '', 1)
    cleaned = cleaned.replace('H-', '', 1).replace('h-', '', 1).strip()
    if not cleaned:
        return ''
    return f"CH-{cleaned}"


def generate_receiving_serial():
    year = datetime.now().strftime('%Y')
    try:
        candidates = []
        rows = ReceivingChallan.query.filter(ReceivingChallan.serial_no.like(f'%/{year}')).all()
        for r in rows:
            s = (r.serial_no or '').strip()
            m = re.search(r'(\d{1,})', s)
            if m:
                try:
                    candidates.append(int(m.group(1)))
                except Exception:
                    pass

        max_n = max(candidates) if candidates else 0
        first_serial_number = 90 if year == '2026' else 1
        next_n = max(max_n + 1, first_serial_number)
        return f"{next_n:03d}/{year}"
    except Exception:
        return f"001/{year}"


def get_next_pending_inventory_serial(job_no=None):
    query = ReceivingChallan.query
    if job_no:
        query = query.filter_by(order_id=job_no)

    pending_challans = query.order_by(ReceivingChallan.id.asc()).all()
    for challan in pending_challans:
        if challan.serial_no and not Inventory.query.filter_by(serial_no=challan.serial_no).first():
            return challan.serial_no, True

    return generate_receiving_serial(), False


def get_next_serial():
    year = datetime.now().strftime('%Y')
    # Look for serials in Inventory like 'NNN/YYYY'
    try:
        candidates = []
        # select inventory entries that end with '/YEAR' or contain the year
        rows = Inventory.query.filter(Inventory.serial_no.like(f'%/{year}')).all()
        for r in rows:
            s = (r.serial_no or '').strip()
            # extract leading number (digits) before slash or anywhere
            m = re.search(r"(\d{1,})", s)
            if m:
                try:
                    n = int(m.group(1))
                    candidates.append(n)
                except Exception:
                    pass

        max_n = max(candidates) if candidates else 0
        next_n = max_n + 1
        return f"{next_n:03d}/{year}"
    except Exception:
        # fallback
        return f"001/{year}"


def calculate_inventory_received_total(inventory_obj):
    return sum(
        parse_numeric(getattr(inventory_obj, field, 0))
        for field in ('fabric_qty_a', 'fabric_qty_b', 'receive_cut_pcs')
    )


def build_inventory_prefill_from_challan(challan, serial_no):
    if not challan:
        return None

    return SimpleNamespace(
        id=None,
        serial_no=serial_no or challan.serial_no or '',
        recv_date=challan.recv_date or '',
        received_from=challan.received_from or '',
        suppliers=challan.suppliers or '',
        challan_no=challan.challan_no or '',
        place=challan.place or '',
        meter_note=challan.meter_to_cm or '',
        ms='',
        file_no=challan.used_file_no or '',
        fabric_name='',
        fabric_qty_a=challan.fabric_qty_a or '',
        fabric_qty_b=challan.fabric_qty_b or '',
        fabric_quality=challan.fabric_quality or '',
        cut_size_header='',
        width=challan.width or '',
        req_cutting='',
        receive_cut_pcs=challan.received_cut_pcs or '',
        fabric_for=challan.fabric_for or '',
        consumption=challan.per_dozen_consumption or '',
        req_average='',
        total=calculate_inventory_received_total(challan)
    )


    

@app.route('/manager/receiving-challan', methods=['GET', 'POST'])
def receiving_challan():
    if not session.get('role'):
        return redirect(url_for('index'))

    job_no = request.args.get('job_no') or request.args.get('order_id') or request.form.get('job_no', '')
    edit_id = request.args.get('edit_id')
    order = Order.query.filter_by(job_no=job_no).first() if job_no else None
    editing_challan = None
    departments = Department.query.order_by(func.lower(Department.name)).all()

    if request.method == 'POST':
        challan_id = request.form.get('challan_id')
        if challan_id and (
            session.get('role') not in ('owner', 'manager') or is_read_only_profile()
        ):
            return reject_read_only_edit('Only the owner and manager can update saved receiving challans.')
        serial_no = request.form.get('serial_no') or generate_receiving_serial()
        supplier_value = request.form.get('suppliers', '')

        fabric_qty_a_value = request.form.get('fabric_qty_a', '').strip()
        fabric_qty_b_value = request.form.get('fabric_qty_b', '').strip()
        received_cut_pcs_value = request.form.get('received_cut_pcs', '').strip()
        uploaded_image = request.files.get('image_file')
        image_path = None
        if uploaded_image and uploaded_image.filename:
            extension = uploaded_image.filename.rsplit('.', 1)[-1].lower() if '.' in uploaded_image.filename else ''
            if extension not in {'png', 'jpg', 'jpeg', 'webp'}:
                flash('Only JPG, PNG, JPEG, and WEBP images are allowed.', 'danger')
            else:
                filename = secure_filename(uploaded_image.filename)
                filename = f"receiving_challan_{datetime.utcnow().strftime('%Y%m%d%H%M%S%f')}_{filename}"
                uploaded_image.save(os.path.join(app.config['UPLOAD_FOLDER'], filename))
                image_path = f"/static/uploads/{filename}"

        def parse_numeric(value):
            try:
                return float(value)
            except (TypeError, ValueError):
                return 0.0

        total_value = parse_numeric(fabric_qty_a_value) + parse_numeric(fabric_qty_b_value) + parse_numeric(received_cut_pcs_value)
        has_any_value = bool(fabric_qty_a_value or fabric_qty_b_value or received_cut_pcs_value)

        if not has_any_value or total_value <= 0:
            flash('Total cannot be zero. Please enter at least one value in Fabric Quantity A, Fabric Quantity B, or Received Cut Pcs.', 'danger')
            form_challan = SimpleNamespace(
                id=challan_id or None,
                order_id=job_no,
                serial_no=serial_no,
                recv_date=request.form.get('recv_date', ''),
                suppliers=supplier_value,
                challan_no=request.form.get('challan_no', ''),
                fabric_quality=request.form.get('fabric_quality', ''),
                width=request.form.get('width', ''),
                fabric_for=request.form.get('fabric_for', ''),
                used_file_no=(request.form.get('used_file_no', '') or (order.file_no if order else '')),
                place=request.form.get('place', ''),
                reciever_name=request.form.get('reciever_name', ''),
                per_dozen_consumption=request.form.get('per_dozen_consumption', ''),
                required_ctn_bails=request.form.get('required_ctn_bails', ''),
                received_from=request.form.get('received_from', ''),
                meter_to_cm=request.form.get('meter_to_cm', ''),
                fabric_qty_a=fabric_qty_a_value,
                fabric_qty_b=fabric_qty_b_value,
                received_cut_pcs=received_cut_pcs_value,
                total=total_value,
                rolls=request.form.get('rolls', ''),
                vehicle_no=request.form.get('vehicle_no', ''),
                delivered_by=request.form.get('delivered_by', ''),
                driver_cell_no=request.form.get('driver_cell_no', ''),
                image_file=image_path
            )
            return render_template(
                'receiving_challan.html',
                selected_job=job_no,
                order=order,
                serial_no=serial_no,
                editing_challan=form_challan,
                departments=departments
            )

        normalized_challan_no = normalize_challan_number(request.form.get('challan_no', ''))

        if challan_id:
            editing_challan = ReceivingChallan.query.get(challan_id)
            if editing_challan:
                editing_challan.order_id = job_no
                editing_challan.serial_no = serial_no
                editing_challan.recv_date = request.form.get('recv_date', '')
                editing_challan.suppliers = supplier_value
                editing_challan.challan_no = normalized_challan_no
                editing_challan.fabric_quality = request.form.get('fabric_quality', '')
                editing_challan.width = request.form.get('width', '')
                editing_challan.fabric_for = request.form.get('fabric_for', '')
                editing_challan.used_file_no = request.form.get('used_file_no', '') or (order.file_no if order else '')
                editing_challan.place = request.form.get('place', '')
                editing_challan.reciever_name = request.form.get('reciever_name', '')
                editing_challan.per_dozen_consumption = request.form.get('per_dozen_consumption', '')
                editing_challan.required_ctn_bails = request.form.get('required_ctn_bails', '')
                editing_challan.received_from = request.form.get('received_from', '')
                editing_challan.meter_to_cm = request.form.get('meter_to_cm', '')
                editing_challan.fabric_qty_a = fabric_qty_a_value
                editing_challan.fabric_qty_b = fabric_qty_b_value
                editing_challan.received_cut_pcs = received_cut_pcs_value
                editing_challan.total = total_value
                editing_challan.rolls = request.form.get('rolls', '')
                editing_challan.vehicle_no = request.form.get('vehicle_no', '')
                editing_challan.delivered_by = request.form.get('delivered_by', '')
                editing_challan.driver_cell_no = request.form.get('driver_cell_no', '')
                if image_path:
                    editing_challan.image_file = image_path
                db.session.commit()
                flash('Receiving challan updated successfully.', 'success')
                return redirect(url_for('inventory', job_no=job_no, serial_no=serial_no))

            flash('Receiving challan not found.', 'danger')
            return redirect(url_for('receiving_challan', job_no=job_no))

        new_challan = ReceivingChallan(
            order_id=job_no,
            serial_no=serial_no,
            recv_date=request.form.get('recv_date', ''),
            suppliers=supplier_value,
            challan_no=normalized_challan_no,
            fabric_quality=request.form.get('fabric_quality', ''),
            width=request.form.get('width', ''),
            fabric_for=request.form.get('fabric_for', ''),
            used_file_no=(request.form.get('used_file_no', '') or (order.file_no if order else '')),
            place=request.form.get('place', ''),
            reciever_name=request.form.get('reciever_name', ''),
            per_dozen_consumption=request.form.get('per_dozen_consumption', ''),
            required_ctn_bails=request.form.get('required_ctn_bails', ''),
            received_from=request.form.get('received_from', ''),
            meter_to_cm=request.form.get('meter_to_cm', ''),
            fabric_qty_a=fabric_qty_a_value,
            fabric_qty_b=fabric_qty_b_value,
            received_cut_pcs=received_cut_pcs_value,
            total=total_value,
            rolls=request.form.get('rolls', ''),
            vehicle_no=request.form.get('vehicle_no', ''),
            delivered_by=request.form.get('delivered_by', ''),
            driver_cell_no=request.form.get('driver_cell_no', ''),
            image_file=image_path
        )
        db.session.add(new_challan)
        db.session.commit()
        flash('Receiving challan saved successfully.', 'success')
        return redirect(url_for('inventory', job_no=job_no, serial_no=serial_no))

    if edit_id:
        editing_challan = ReceivingChallan.query.get(edit_id)
        if editing_challan:
            job_no = editing_challan.order_id or job_no
            order = Order.query.filter_by(job_no=job_no).first() if job_no else None
            serial_no = editing_challan.serial_no or generate_receiving_serial()
        else:
            flash('Receiving challan not found.', 'danger')
            serial_no = generate_receiving_serial()
    else:
        serial_no = generate_receiving_serial()

    return render_template(
        'receiving_challan.html',
        selected_job=job_no,
        order=order,
        serial_no=serial_no,
        editing_challan=editing_challan,
        departments=departments
    )



@app.route('/manager/receiving-challan/print')
def receiving_challan_print():
    if not session.get('role'):
        return redirect(url_for('index'))

    job_no = request.args.get('job_no') or request.args.get('order_id')
    serial_no = request.args.get('serial_no')
    challan = None
    if serial_no:
        if job_no:
            challan = ReceivingChallan.query.filter_by(order_id=job_no, serial_no=serial_no).first()
        else:
            challan = ReceivingChallan.query.filter_by(serial_no=serial_no).first()

    if not challan:
        flash('Receiving challan not found for printing.', 'danger')
        return redirect(url_for('receiving_challan', job_no=job_no))

    return render_template('receiving_challan_print.html', challan=challan)




def get_article_order_numbers(job_no):
    if not job_no:
        return set()

    order = Order.query.filter_by(job_no=job_no).first()
    if not order:
        return {job_no}

    party_name = (order.name or getattr(getattr(order, 'article_ref', None), 'party_name', '') or '').strip()
    article_name = (order.article_name or getattr(getattr(order, 'article_ref', None), 'article_name', '') or '').strip()
    color = (order.color or getattr(getattr(order, 'article_ref', None), 'color', '') or '').strip()
    article_no = order.article or ''
    normalized_article_no = display_article_no(article_no)

    article_filters = []
    if order.article_id:
        article_filters.append(Order.article_id == order.article_id)
    if article_no:
        article_filters.extend([
            func.lower(Order.article) == func.lower(article_no),
            func.lower(Order.article) == func.lower(normalized_article_no),
        ])
    if party_name and article_name and color:
        article_filters.append(
            and_(
                func.lower(Order.name) == func.lower(party_name),
                func.lower(Order.article_name) == func.lower(article_name),
                func.lower(Order.color) == func.lower(color),
            )
        )

    order_numbers = {
        linked_order.job_no
        for linked_order in Order.query.filter(or_(*article_filters)).all()
        if linked_order.job_no
    }
    order_numbers.add(job_no)
    return order_numbers


def display_order_number(order_number):
    match = re.search(r'(\d+)$', str(order_number or ''))
    return match.group(1) if match else (order_number or '')


app.jinja_env.globals['display_order_number'] = display_order_number


@app.route('/manager/saved-receiving-challans')
def saved_receiving_challans():
    if not session.get('role'):
        return redirect(url_for('index'))

    job_no = request.args.get('job_no') or request.args.get('order_id') or request.args.get('auto_job')
    article_order_numbers = get_article_order_numbers(job_no)
    challans = (
        ReceivingChallan.query.filter(ReceivingChallan.order_id.in_(article_order_numbers))
        .order_by(ReceivingChallan.id.desc()).all()
        if article_order_numbers
        else ReceivingChallan.query.order_by(ReceivingChallan.id.desc()).all()
    )
    return render_template('saved_receiving_challans.html', order_id=job_no, challans=challans)


@app.route('/manager/delete-receiving-challan', methods=['POST'])
def delete_receiving_challan():
    if not session.get('role'):
        return redirect(url_for('index'))
    if session.get('role') not in ('owner', 'manager') or is_read_only_profile():
        return reject_read_only_edit('Only the owner and manager can delete receiving challans.')

    challan_id = request.form.get('challan_id')
    job_no = request.form.get('job_no', '')
    challan = ReceivingChallan.query.get(challan_id) if challan_id else None

    if challan:
        db.session.delete(challan)
        db.session.commit()
        flash('Receiving challan deleted successfully.', 'success')
    else:
        flash('Receiving challan not found.', 'danger')

    return redirect(url_for('saved_receiving_challans', job_no=job_no))


@app.route('/manager/delete-inventory', methods=['POST'])
def delete_inventory():
    if not session.get('role'):
        return redirect(url_for('index'))
    if session.get('role') not in ('owner', 'manager') or is_read_only_profile():
        return reject_read_only_edit('Only the owner and manager can delete inventory records.')

    inventory_id = request.form.get('inventory_id')
    job_no = request.form.get('job_no', '')
    inventory = Inventory.query.get(inventory_id) if inventory_id else None

    if inventory:
        db.session.delete(inventory)
        db.session.commit()
        flash('Inventory deleted successfully.', 'success')
    else:
        flash('Inventory not found.', 'danger')

    return redirect(url_for('saved_inventory', job_no=job_no))

@app.route('/manager/cutting-sheet', methods=['GET', 'POST'])
def cutting_sheet():
    if not session.get('role'):
        return redirect(url_for('index'))

    job_no = request.args.get('job_no') or request.args.get('order_id') or request.args.get('auto_job') or request.form.get('job_no', '')
    edit_id = request.args.get('edit_id') or request.form.get('cutting_sheet_id', '')
    cutting_sheet_serial_no = generate_cutting_sheet_serial()
    cutting_sheet = None
    cutting_sheet_rows = []
    cutting_sheet_row_map = {}

    order = Order.query.filter_by(job_no=job_no).first() if job_no else None
    if not order:
        flash('Order not found. Please open a valid order first.', 'danger')
        return redirect(url_for('index'))

    order_inventories = Inventory.query.filter_by(order_id=job_no).order_by(Inventory.id.asc()).all()
    article_order_numbers = get_article_order_numbers(job_no)
    article_inventories = Inventory.query.filter(
        Inventory.order_id.in_(article_order_numbers)
    ).order_by(Inventory.id.asc()).all()
    inventory = order_inventories[0] if order_inventories else (article_inventories[0] if article_inventories else None)
    inventory_serials = [inv.serial_no for inv in article_inventories if inv.serial_no]
    next_cut_no = get_next_cut_no_for_order(job_no)
    order_month_year = ''
    if order and order.date:
        try:
            parsed_date = datetime.strptime(order.date, '%Y-%m-%d')
            order_month_year = parsed_date.strftime('%b %Y')
        except ValueError:
            order_month_year = order.date

    current_month_year = datetime.now().strftime('%b %Y')

    def numeric_meter(value):
        try:
            return float(value or 0)
        except (TypeError, ValueError):
            return 0.0

    def split_inventory_serials(value):
        raw_value = (value or '').strip()
        if not raw_value:
            return []
        if '-' not in raw_value or '/' not in raw_value:
            return [raw_value]
        number_part, year_part = raw_value.rsplit('/', 1)
        return [f'{part}/{year_part}' for part in number_part.split('-') if part]

    def combine_inventory_serials(primary_serial, secondary_serial=''):
        primary = (primary_serial or '').strip()
        secondary = (secondary_serial or '').strip()
        if not secondary or secondary == primary:
            return primary
        if '/' in primary and '/' in secondary:
            primary_number, primary_year = primary.rsplit('/', 1)
            secondary_number, secondary_year = secondary.rsplit('/', 1)
            if primary_year == secondary_year:
                return f'{primary_number}-{secondary_number}/{primary_year}'
        return f'{primary}-{secondary}'

    def prior_cut_sheets(current_cut_no, inventory_serial=None, current_sheet_id=None):
        prior = []
        for sheet in CuttingSheet.query.filter_by(order_id=job_no).all():
            if current_sheet_id and sheet.id == current_sheet_id:
                continue
            if inventory_serial and inventory_serial not in split_inventory_serials(sheet.inventory_serial_no):
                continue
            try:
                sheet_cut_no = int(str(sheet.cut_no))
            except (TypeError, ValueError):
                continue
            if sheet_cut_no < current_cut_no:
                prior.append(sheet)
        return sorted(prior, key=lambda sheet: int(str(sheet.cut_no)))

    def inventory_balances_before_cut(current_cut_no, current_sheet_id=None):
        balances = {}
        current_cut_date = (
            (cutting_sheet.cut_date if cutting_sheet else None)
            or request.form.get('cut_date')
            or datetime.now().strftime('%Y-%m-%d')
        )
        for inv in article_inventories:
            if not inv.serial_no:
                continue
            state = calculate_inventory_consumption_state(
                inv,
                before_cut_no=current_cut_no,
                order_id=job_no,
                before_date=current_cut_date,
            )
            # Re-active replaces the rejected portion of A, so it is part of
            # the usable O/B exactly once, not an additional quantity.
            total_received = state['a_remaining'] + state['reactive_remaining']
            if inventory_b_active_for_cut(inv, current_cut_no, job_no):
                total_received += state['b_remaining']
            balances[inv.serial_no] = max(0.0, total_received)

        return balances

    if request.method == 'POST':
        required_left_info_fields = {
            'cut_date': 'Cut date',
            'calc_cut_size': 'Cut size',
            'calc_factor_1': 'Cut size factor',
            'pcs_in_row': 'PCS in row',
            'range_margin': 'Range margin',
            'pcs_in_range': 'PCS in range',
            'avg_other': 'Width',
            'cutter_name': 'Cutter name',
            'fabric_issue': 'Fabric issue',
            'inventory_serial_no': 'Primary inventory',
            'use_fabric_ch': 'Use fabric CH',
            'asst_cutter_name': 'Assistant cutter name',
            'issued_by': 'Issued by',
            'palla_check_by': 'Palla check by',
        }
        avg_99 = (request.form.get('avg_99') or '').strip()
        avg_100 = (request.form.get('avg_100') or '').strip()
        pcs_in_row = (request.form.get('pcs_in_row') or '').strip()
        pcs_in_range = (request.form.get('pcs_in_range') or '').strip()
        validation_errors = []
        for field_name, field_label in required_left_info_fields.items():
            if not (request.form.get(field_name) or '').strip():
                validation_errors.append(field_label)
        if avg_99:
            try:
                avg_99_value = float(avg_99)
                if avg_99_value < 0 or avg_99_value > 99:
                    validation_errors.append('99 value must be between 0 and 99')
                else:
                    avg_99 = str(avg_99_value)
            except ValueError:
                validation_errors.append('99 value must be numeric')
        if avg_100:
            try:
                avg_100_value = float(avg_100)
                if avg_100_value != 100:
                    validation_errors.append('100 value must be exactly 100')
            except ValueError:
                validation_errors.append('100 value must be numeric')
        if bool(avg_99) == bool(avg_100):
            validation_errors.append('Please fill either 99 or 100')
        if validation_errors:
            flash(f"Please fill the required cutting-sheet fields: {', '.join(validation_errors)}.", 'danger')
            redirect_args = {'order_id': job_no}
            if edit_id:
                redirect_args['edit_id'] = edit_id
            return redirect(url_for('cutting_sheet', **redirect_args))

        if edit_id and is_read_only_profile():
            return reject_read_only_edit()
        if edit_id:
            cutting_sheet = CuttingSheet.query.filter_by(id=edit_id, order_id=job_no).first()
            if cutting_sheet and CuttingTransfer.query.filter(
                CuttingTransfer.source_cutting_sheet_id == cutting_sheet.id
            ).first():
                flash('This cutting sheet is linked to a transfer and cannot be edited.', 'danger')
                return redirect(url_for('saved_cutting_sheets', job_no=job_no))
        if not cutting_sheet:
            cutting_sheet = CuttingSheet(order_id=job_no)
            cutting_sheet.serial_no = request.form.get('cutting_sheet_serial_no') or generate_cutting_sheet_serial()
            cutting_sheet.cut_no = request.form.get('cut_no') or next_cut_no
        else:
            cutting_sheet.serial_no = request.form.get('cutting_sheet_serial_no') or cutting_sheet.serial_no
            cutting_sheet.cut_no = request.form.get('cut_no') or cutting_sheet.cut_no

        incoming_transfer = (
            CuttingTransfer.query.filter_by(
                destination_cutting_sheet_id=cutting_sheet.id,
                reversed_at=None,
            ).first()
            if cutting_sheet.id else None
        )

        cutting_sheet.cut_size = request.form.get('calc_cut_size', '')
        cutting_sheet.factor_1 = request.form.get('calc_factor_1', '')
        cutting_sheet.factor_2 = request.form.get('calc_factor_2', '')
        cutting_sheet.total = request.form.get('calc_total', '')
        cutting_sheet.divisor = request.form.get('calc_divisor', '')
        cutting_sheet.result = request.form.get('calc_result', '')
        cutting_sheet.range_width = request.form.get('range_width', '')
        cutting_sheet.range_height = request.form.get('range_height', '')
        cutting_sheet.range_area = request.form.get('range_area', '')
        cutting_sheet.pcs_in_row = request.form.get('pcs_in_row', '')
        cutting_sheet.range_margin = request.form.get('range_margin', '')
        cutting_sheet.range_result = request.form.get('range_result', '')
        cutting_sheet.pcs_in_range = request.form.get('pcs_in_range', '')
        cutting_sheet.avg_99 = request.form.get('avg_99', '')
        cutting_sheet.avg_100 = request.form.get('avg_100', '')
        cutting_sheet.avg_other = request.form.get('avg_other', '')
        cutting_sheet.cutter_name = request.form.get('cutter_name', '')
        cutting_sheet.fabric_issue = request.form.get('fabric_issue', '')
        previous_cut_inventory_serials = split_inventory_serials(cutting_sheet.inventory_serial_no)
        cutting_sheet.inventory_serial_no = request.form.get('inventory_serial_no', '')
        cutting_sheet.use_fabric_ch = request.form.get('use_fabric_ch', '')
        cutting_sheet.asst_cutter_name = request.form.get('asst_cutter_name', '')
        cutting_sheet.palla_check_by = request.form.get('palla_check_by', '')
        cutting_sheet.summary_total_pcs = request.form.get('summary_total_pcs', '')
        cutting_sheet.summary_avg_pcs = request.form.get('summary_avg_pcs', '')
        cutting_sheet.balance_cutting = request.form.get('balance_cutting', '')
        cutting_sheet.total_cutting = request.form.get('total_cutting', '')
        cutting_sheet.to_date_production = request.form.get('to_date_production', '')
        # Save shortage from the mini PCS field on row 22
        cutting_sheet.shortage = request.form.get('mini_pcs_22', '')
        # Save shift-to-next-cut using the model's column name
        cutting_sheet.shift_to_next_cut = request.form.get('shift_to_next_cut', '')
        # Save total meter (fabric) calculated client-side
        table_total_meter = numeric_meter(request.form.get('total_meter'))
        requested_inventory_serial = (request.form.get('inventory_serial_no') or '').strip()
        requested_secondary_serial = (request.form.get('secondary_inventory_serial') or '').strip()
        stored_inventory_serials = split_inventory_serials(cutting_sheet.inventory_serial_no)
        if not requested_inventory_serial and stored_inventory_serials:
            requested_inventory_serial = stored_inventory_serials[0]
        if not requested_secondary_serial and len(stored_inventory_serials) > 1:
            requested_secondary_serial = stored_inventory_serials[1]
        if requested_secondary_serial == requested_inventory_serial:
            requested_secondary_serial = ''
        selected_inventory = Inventory.query.filter_by(serial_no=requested_inventory_serial).first() if requested_inventory_serial else inventory
        secondary_inventory = Inventory.query.filter_by(serial_no=requested_secondary_serial).first() if requested_secondary_serial else None
        if selected_inventory:
            inventory = selected_inventory
            requested_inventory_serial = selected_inventory.serial_no or requested_inventory_serial
        if requested_secondary_serial and not secondary_inventory:
            flash('The selected secondary inventory was not found.', 'danger')
            redirect_args = {'order_id': job_no}
            if edit_id:
                redirect_args['edit_id'] = edit_id
            return redirect(url_for('cutting_sheet', **redirect_args))
        try:
            current_cut_no = int(str(cutting_sheet.cut_no))
        except (TypeError, ValueError):
            current_cut_no = next_cut_no
        available_inventory_balances = inventory_balances_before_cut(current_cut_no, cutting_sheet.id)
        fallback_inventory = None
        fallback_pool = None
        for inv in article_inventories:
            if not inv.serial_no:
                continue
            if inv.serial_no in {requested_inventory_serial, requested_secondary_serial}:
                continue
            pool = calculate_inventory_reactive_fallback_pool(inv)
            if pool['active'] and pool['fallback_balance'] > 0:
                fallback_inventory = inv
                fallback_pool = pool
                break
        fallback_total_meter = fallback_pool['fallback_balance'] if fallback_pool else 0.0
        primary_opening_balance = available_inventory_balances.get(requested_inventory_serial, 0.0)
        secondary_total_meter = available_inventory_balances.get(requested_secondary_serial, 0.0) if secondary_inventory else 0.0
        opening_balance = primary_opening_balance + fallback_total_meter + secondary_total_meter
        fabric_issue_amount = numeric_meter(request.form.get('fabric_issue'))
        if fabric_issue_amount > opening_balance:
            message = (
                f'Insufficient fabric. Fabric issue is {fabric_issue_amount:.2f} meters, '
                f'but fabric O/B is {opening_balance:.2f} meters.'
            )
            if not secondary_inventory:
                message += ' Please select secondary inventory.'
            flash(message, 'danger')
            redirect_args = {'order_id': job_no}
            if edit_id:
                redirect_args['edit_id'] = edit_id
            return redirect(url_for('cutting_sheet', **redirect_args))
        balance_after_cut = opening_balance - table_total_meter
        if balance_after_cut < 0:
            flash(
                f'Insufficient fabric. Current opening balance is {opening_balance:.2f} meters, '
                f'but this cut uses {table_total_meter:.2f} meters. Select a secondary inventory.',
                'danger'
            )
            redirect_args = {'order_id': job_no}
            if edit_id:
                redirect_args['edit_id'] = edit_id
            return redirect(url_for('cutting_sheet', **redirect_args))
        combined_inventory_serial = combine_inventory_serials(requested_inventory_serial, requested_secondary_serial)
        cutting_sheet.inventory_serial_no = combined_inventory_serial
        inventory_total_meter = numeric_meter(inventory.fabric_qty_a if inventory else 0)
        cutting_sheet.total_meter = f'{table_total_meter:.2f}' if request.form.get('total_meter') else ''
        cutting_sheet.total_palla = request.form.get('total_palla', '')
        table_total_pcs = numeric_meter(request.form.get('total_pcs'))
        if incoming_transfer:
            cutting_sheet.total_pcs = f'{table_total_pcs + incoming_transfer.quantity:.0f}'
        else:
            cutting_sheet.total_pcs = request.form.get('total_pcs', '')
        cutting_sheet.fabric_meter = f'{inventory_total_meter:.2f}' if selected_inventory else request.form.get('fabric_meter', '')
        cutting_sheet.mini_palla_22 = request.form.get('mini_palla_22', '')
        cutting_sheet.mini_pcs_22 = request.form.get('mini_pcs_22', '')
        cutting_sheet.mini_cp_22 = request.form.get('mini_cp_22', '')
        cutting_sheet.mini_palla_22_grey = request.form.get('mini_palla_22_grey', '')
        cutting_sheet.mini_pcs_22_grey = request.form.get('mini_pcs_22_grey', '')
        cutting_sheet.mini_cp_22_grey = request.form.get('mini_cp_22_grey', '')
        cutting_sheet.remarks = request.form.get('remarks', '')
        cutting_sheet.issued_by = request.form.get('issued_by', '')
        cutting_sheet.department = request.form.get('department', '')
        cutting_sheet.bundle = request.form.get('bundle', '')
        cutting_sheet.quantity = request.form.get('quantity', '')
        cutting_sheet.issue_to_sv = request.form.get('issue_to_sv', '')
        cutting_sheet.cut_date = request.form.get('cut_date', '')
        cutting_sheet.issue_date = request.form.get('issue_date', '')
        cutting_sheet.time_field = request.form.get('time_field', '')
        cutting_sheet.balance_fabric = f'{balance_after_cut:.2f}' if selected_inventory else request.form.get('balance_fabric', '')

        if not cutting_sheet.id:
            db.session.add(cutting_sheet)
        db.session.flush()

        CuttingSheetRow.query.filter_by(cutting_sheet_id=cutting_sheet.id).delete()
        for i in range(1, 23):
            meter = request.form.get(f'meter_{i}', '').strip()
            palla = request.form.get(f'palla_{i}', '').strip()
            pcs = request.form.get(f'pcs_{i}', '').strip()
            cp = request.form.get(f'cp_{i}', '').strip() if i <= 19 else ''
            if meter or palla or pcs or cp:
                db.session.add(CuttingSheetRow(
                    cutting_sheet_id=cutting_sheet.id,
                    idx=i,
                    meter=meter,
                    palla=palla,
                    pcs=pcs,
                    cp=cp
                ))

        if selected_inventory and selected_inventory.id:
            fabric_issue = numeric_meter(cutting_sheet.fabric_issue)
            total_cutting_pcs = numeric_meter(cutting_sheet.quantity)
            total_cut_pcs = numeric_meter(cutting_sheet.mini_cp_22_grey)
            total_wastage = numeric_meter(cutting_sheet.mini_cp_22)
            total_palla = numeric_meter(cutting_sheet.total_palla)
            range_result_value = numeric_meter(cutting_sheet.range_result)
            order_file_no = (order.file_no if order else '') or ''

            inventory_allocations = []
            remaining_usage = table_total_meter
            for allocation_inventory in (selected_inventory, fallback_inventory, secondary_inventory):
                if not allocation_inventory or not allocation_inventory.id:
                    continue
                opening_balance = available_inventory_balances.get(
                    allocation_inventory.serial_no,
                    numeric_meter(allocation_inventory.fabric_qty_a),
                )
                if (
                    fallback_inventory
                    and allocation_inventory.serial_no == fallback_inventory.serial_no
                    and fallback_pool
                ):
                    opening_balance = fallback_pool['fallback_balance']
                allocated_usage = min(opening_balance, remaining_usage)
                if allocated_usage > 0:
                    inventory_allocations.append((allocation_inventory, opening_balance, allocated_usage))
                    remaining_usage -= allocated_usage

            mirrored_serials = set(previous_cut_inventory_serials)
            mirrored_serials.update(
                allocation_inventory.serial_no
                for allocation_inventory, _, _ in inventory_allocations
                if allocation_inventory.serial_no
            )
            mirrored_inventories = Inventory.query.filter(Inventory.serial_no.in_(mirrored_serials)).all()
            mirrored_inventory_ids = [inv.id for inv in mirrored_inventories if inv.id]
            if mirrored_inventory_ids:
                InventoryRow.query.filter(
                    InventoryRow.inventory_id.in_(mirrored_inventory_ids),
                    InventoryRow.sno == cutting_sheet.serial_no,
                    InventoryRow.cut_no == cutting_sheet.cut_no,
                ).delete(synchronize_session=False)

            allocated_cutting_pcs = 0
            allocated_cut_pcs = 0
            allocated_wastage = 0
            allocated_palla = 0.0
            allocated_fabric_issue = 0.0
            for allocation_index, (allocation_inventory, opening_balance, fabric_use) in enumerate(inventory_allocations):
                is_last_allocation = allocation_index == len(inventory_allocations) - 1
                usage_ratio = fabric_use / table_total_meter if table_total_meter else 0.0
                if is_last_allocation:
                    row_cutting_pcs = total_cutting_pcs - allocated_cutting_pcs
                    row_cut_pcs = total_cut_pcs - allocated_cut_pcs
                    row_wastage = total_wastage - allocated_wastage
                    row_palla = total_palla - allocated_palla
                    row_fabric_issue = fabric_issue - allocated_fabric_issue
                else:
                    row_cutting_pcs = round(total_cutting_pcs * usage_ratio)
                    row_cut_pcs = round(total_cut_pcs * usage_ratio)
                    row_wastage = round(total_wastage * usage_ratio, 2)
                    row_palla = total_palla * usage_ratio
                    row_fabric_issue = fabric_issue * usage_ratio

                allocated_cutting_pcs += row_cutting_pcs
                allocated_cut_pcs += row_cut_pcs
                allocated_wastage += row_wastage
                allocated_palla += row_palla
                allocated_fabric_issue += row_fabric_issue
                fabric_req = (
                    range_result_value * row_palla / 39.35
                    if range_result_value and row_palla
                    else fabric_use
                )
                fabric_return = row_fabric_issue - fabric_use
                next_idx = max(
                    [row.idx or 0 for row in InventoryRow.query.filter_by(inventory_id=allocation_inventory.id).all()]
                    or [0]
                ) + 1
                db.session.add(InventoryRow(
                    inventory_id=allocation_inventory.id,
                    idx=next_idx,
                    date=cutting_sheet.cut_date or None,
                    item=(order.style if order else '') or None,
                    sno=cutting_sheet.serial_no or None,
                    file_no=order_file_no or None,
                    cut_no=cutting_sheet.cut_no or None,
                    cut_size=allocation_inventory.cut_size_header or None,
                    cutting_pcs=int(row_cutting_pcs) if row_cutting_pcs else None,
                    fabric_req=f'{fabric_req:.2f}',
                    fabric_issue=f'{row_fabric_issue:.2f}',
                    issue_by=cutting_sheet.issued_by or None,
                    fabric_return=f'{fabric_return:.2f}',
                    fabric_use=f'{fabric_use:.2f}',
                    wastage=f'{row_wastage:.2f}',
                    cut_pcs=int(row_cut_pcs) if row_cut_pcs else None,
                    balance=f'{(opening_balance - fabric_use):.2f}',
                ))
        db.session.commit()
        flash('Cutting sheet saved successfully.', 'success')
        return redirect(url_for('bundle_stickers', cutting_sheet_id=cutting_sheet.id))

    if edit_id:
        cutting_sheet = CuttingSheet.query.filter_by(id=edit_id, order_id=job_no).first()
        if cutting_sheet:
            cutting_sheet_serial_no = cutting_sheet.serial_no or cutting_sheet_serial_no
            cutting_sheet_rows = CuttingSheetRow.query.filter_by(cutting_sheet_id=cutting_sheet.id).order_by(CuttingSheetRow.idx.asc()).all()
            cutting_sheet_row_map = {row.idx: row for row in cutting_sheet_rows}
        else:
            flash('Cutting sheet not found.', 'danger')
    transfer_origin = (
        CuttingTransfer.query.filter_by(destination_cutting_sheet_id=cutting_sheet.id)
        .order_by(CuttingTransfer.created_at.desc(), CuttingTransfer.id.desc())
        .first()
        if cutting_sheet and cutting_sheet.id else None
    )
    # Compute previous total_cutting for this order (sum of total_cutting from earlier cuts)
    previous_total_cutting = 0.0
    try:
        # Determine current cut number (editing or creating)
        current_cut_no = None
        if cutting_sheet and cutting_sheet.cut_no:
            try:
                current_cut_no = int(str(cutting_sheet.cut_no))
            except Exception:
                current_cut_no = None
        if current_cut_no is None:
            try:
                current_cut_no = int(str(next_cut_no))
            except Exception:
                current_cut_no = None

        sheets = CuttingSheet.query.filter_by(order_id=job_no).all()
        for s in sheets:
            # skip the current sheet when editing
            if cutting_sheet and s.id == cutting_sheet.id:
                continue
            try:
                s_cut_no = int(str(s.cut_no)) if s.cut_no is not None else None
            except Exception:
                s_cut_no = None
            # include sheets with numeric cut_no less than current_cut_no, or include all if current_cut_no unknown
            if s_cut_no is None or current_cut_no is None or (s_cut_no < current_cut_no):
                try:
                    val = float(s.total_cutting) if s.total_cutting not in (None, '') else 0.0
                except Exception:
                    val = 0.0
                previous_total_cutting += val
    except Exception:
        previous_total_cutting = 0.0
    # Compute previous total_meter for this order (sum of total_meter from earlier cuts)
    previous_total_meter = 0.0
    try:
        for s in sheets:
            # skip the current sheet when editing
            if cutting_sheet and s.id == cutting_sheet.id:
                continue
            try:
                s_cut_no = int(str(s.cut_no)) if s.cut_no is not None else None
            except Exception:
                s_cut_no = None
            if s_cut_no is None or current_cut_no is None or (s_cut_no < current_cut_no):
                try:
                    valm = float(s.total_meter) if s.total_meter not in (None, '') else 0.0
                except Exception:
                    valm = 0.0
                previous_total_meter += valm
    except Exception:
        previous_total_meter = 0.0

    # Carry forward the last remaining fabric balance from the previous cut as the starting
    # balance for the next cut, and preserve the previous inventory serial so the UI can tell
    # whether the user has kept the same inventory or switched to a new one.
    previous_balance_fabric = 0.0
    previous_inventory_serial_no = ''
    try:
        previous_sheets = []
        for s in sheets:
            if cutting_sheet and s.id == cutting_sheet.id:
                continue
            try:
                s_cut_no = int(str(s.cut_no)) if s.cut_no is not None else None
            except Exception:
                s_cut_no = None
            if s_cut_no is None or current_cut_no is None or (s_cut_no < current_cut_no):
                previous_sheets.append(s)

        if previous_sheets:
            previous_sheets.sort(key=lambda s: (int(str(s.cut_no)) if str(s.cut_no).isdigit() else -1), reverse=True)
            latest_prev_sheet = previous_sheets[0]
            previous_inventory_serial_no = latest_prev_sheet.inventory_serial_no or ''
            try:
                previous_balance_fabric = float(latest_prev_sheet.balance_fabric) if latest_prev_sheet.balance_fabric not in (None, '') else 0.0
            except Exception:
                previous_balance_fabric = 0.0
    except Exception:
        previous_balance_fabric = 0.0
        previous_inventory_serial_no = ''

    stored_inventory_serials = split_inventory_serials(cutting_sheet.inventory_serial_no if cutting_sheet else '')
    previous_inventory_serials = split_inventory_serials(previous_inventory_serial_no)
    order_inventory_serials = inventory_serials[:]
    prior_inventory_balances = inventory_balances_before_cut(current_cut_no or next_cut_no, None)

    def first_available_inventory_serial(fallback_serials=None):
        serial_candidates = fallback_serials if fallback_serials else order_inventory_serials
        for serial in serial_candidates:
            if prior_inventory_balances.get(serial, 0.0) > 0:
                return serial
        return ''

    selected_inventory_serial = (
        stored_inventory_serials[0]
        if stored_inventory_serials
        else (previous_inventory_serials[0] if previous_inventory_serials else first_available_inventory_serial())
    )
    selected_secondary_inventory_serial = stored_inventory_serials[1] if len(stored_inventory_serials) > 1 else ''
    if not cutting_sheet:
        previous_primary = previous_inventory_serials[0] if previous_inventory_serials else ''
        previous_secondary = previous_inventory_serials[1] if len(previous_inventory_serials) > 1 else ''
        primary_balance = prior_inventory_balances.get(previous_primary, 0.0) if previous_primary else 0.0
        secondary_balance = prior_inventory_balances.get(previous_secondary, 0.0) if previous_secondary else 0.0

        if previous_primary and primary_balance <= 0 and secondary_balance > 0:
            selected_inventory_serial = previous_secondary
            selected_secondary_inventory_serial = ''
        elif previous_primary and primary_balance <= 0 and not secondary_balance:
            selected_inventory_serial = first_available_inventory_serial(order_inventory_serials)
            selected_secondary_inventory_serial = ''
        elif selected_inventory_serial and prior_inventory_balances.get(selected_inventory_serial, 0.0) <= 0:
            selected_inventory_serial = first_available_inventory_serial(order_inventory_serials)
            selected_secondary_inventory_serial = ''
        elif not selected_inventory_serial:
            selected_inventory_serial = first_available_inventory_serial(order_inventory_serials)
            selected_secondary_inventory_serial = ''
    if selected_inventory_serial:
        previous_sheets = [
            sheet for sheet in previous_sheets
            if selected_inventory_serial in split_inventory_serials(sheet.inventory_serial_no)
        ]
        if previous_sheets:
            previous_sheets.sort(key=lambda sheet: int(str(sheet.cut_no)) if str(sheet.cut_no).isdigit() else -1)
            previous_balance_fabric = numeric_meter(previous_sheets[-1].balance_fabric)
        else:
            previous_balance_fabric = 0.0
    selected_inventory = Inventory.query.filter_by(serial_no=selected_inventory_serial).first() if selected_inventory_serial else inventory
    selected_secondary_inventory = Inventory.query.filter_by(serial_no=selected_secondary_inventory_serial).first() if selected_secondary_inventory_serial else None
    if selected_inventory:
        inventory = selected_inventory

    display_cut_no = current_cut_no or next_cut_no
    if cutting_sheet and cutting_sheet.id and str(cutting_sheet.cut_no or '').strip().isdigit():
        display_cut_no = int(str(cutting_sheet.cut_no))
    available_inventory_balances = inventory_balances_before_cut(display_cut_no, cutting_sheet.id if cutting_sheet else None)

    if cutting_sheet and cutting_sheet.id and cutting_sheet.balance_fabric not in (None, ''):
        previous_balance_fabric = numeric_meter(cutting_sheet.balance_fabric)
    else:
        previous_balance_fabric = available_inventory_balances.get(selected_inventory_serial, 0.0)

    secondary_inventory_total_meter = (
        available_inventory_balances.get(selected_secondary_inventory_serial, 0.0)
        if selected_secondary_inventory else 0.0
    )
    active_b_total_meter = 0.0
    for active_inventory in (selected_inventory, selected_secondary_inventory):
        if active_inventory and inventory_b_active_for_cut(active_inventory, display_cut_no, job_no):
            active_b_total_meter += max(0.0, numeric_meter(active_inventory.fabric_qty_b))
    inventory_total_meter = (
        numeric_meter(selected_inventory.fabric_qty_a) if selected_inventory else 0.0
    ) + active_b_total_meter
    primary_inventory_total_meter = (
        numeric_meter(selected_inventory.fabric_qty_a)
        if selected_inventory else 0.0
    )
    if selected_inventory and inventory_b_active_for_cut(selected_inventory, display_cut_no, job_no):
        primary_inventory_total_meter += calculate_inventory_consumption_state(
            selected_inventory,
            before_cut_no=display_cut_no,
            order_id=job_no,
        )['b_remaining']
    active_b_quality_remaining = 0.0
    if selected_inventory and inventory_b_active_for_cut(selected_inventory, display_cut_no, job_no):
        active_b_quality_remaining = calculate_inventory_consumption_state(
            selected_inventory,
            before_cut_no=display_cut_no,
            order_id=job_no,
        )['b_remaining']
    opening_balance_fabric = available_inventory_balances.get(selected_inventory_serial, previous_balance_fabric)
    if selected_secondary_inventory_serial:
        opening_balance_fabric += available_inventory_balances.get(selected_secondary_inventory_serial, 0.0)
    current_table_total_meter = numeric_meter(cutting_sheet.total_meter) if cutting_sheet else 0.0
    balance_fabric = opening_balance_fabric - current_table_total_meter
    inventory_balances = available_inventory_balances
    inventory_rejected_balances = {
        inv.serial_no: max(0.0, numeric_meter(inv.rejected_fabric))
        for inv in article_inventories
        if inv.serial_no
    }
    inventory_reactive_balances = {
        inv.serial_no: calculate_inventory_fabric_balances(inv)['reactive_remaining']
        for inv in article_inventories
        if inv.serial_no
    }
    inventory_statuses = {}
    for inv in article_inventories:
        if not inv.serial_no:
            continue
        fabric_status = calculate_inventory_fabric_balances(inv)
        status_parts = []
        if fabric_status['rejected_fabric'] > 0:
            status_parts.append('REJ FAB' if fabric_status['reactive_remaining'] <= 0 else 'REJ')
        if fabric_status['reactive_remaining'] > 0:
            status_parts.append('RE-ACTIVE')
        if fabric_status['left_over_fabric'] > 0:
            status_parts.append('PENDING')

        if status_parts:
            status_class = (
                'inventory-status-rejected'
                if fabric_status['rejected_fabric'] > 0 or fabric_status['reactive_remaining'] > 0
                else 'inventory-status-pending'
            )
            inventory_statuses[inv.serial_no] = {
                'label': ' + '.join(status_parts),
                'class_name': status_class,
                'has_prior_use': fabric_status['used_fabric'] > 0,
            }
        else:
            inventory_statuses[inv.serial_no] = {
                'label': 'FINISHED',
                'class_name': 'inventory-status-finished',
                'has_prior_use': fabric_status['used_fabric'] > 0,
            }

    default_cut_date = datetime.now().strftime('%Y-%m-%d')
    default_issue_date = datetime.now().strftime('%Y-%m-%d')
    return render_template(
        'cutting_sheet.html',
        selected_job=job_no,
        order=order,
        inventory=inventory,
        inventory_serials=inventory_serials,
        selected_secondary_inventory_serial=selected_secondary_inventory_serial,
        order_month_year=order_month_year,
        current_month_year=current_month_year,
        cutting_sheet=cutting_sheet,
        transfer_origin=transfer_origin,
        cutting_sheet_rows=cutting_sheet_rows,
        cutting_sheet_row_map=cutting_sheet_row_map,
        cutting_sheet_serial_no=cutting_sheet_serial_no,
        next_cut_no=next_cut_no,
        previous_total_cutting=previous_total_cutting,
        previous_total_meter=previous_total_meter,
        previous_balance_fabric=previous_balance_fabric,
        previous_inventory_serial_no=previous_inventory_serial_no,
        selected_inventory_serial=selected_inventory_serial,
        inventory_total_meter=inventory_total_meter,
        opening_balance_fabric=opening_balance_fabric,
        balance_fabric=balance_fabric,
        active_b_quality_remaining=active_b_quality_remaining,
        inventory_balances=inventory_balances,
        inventory_rejected_balances=inventory_rejected_balances,
        inventory_reactive_balances=inventory_reactive_balances,
        inventory_statuses=inventory_statuses,
        default_cut_date=default_cut_date,
        default_issue_date=default_issue_date,
        hide_logo=True
    )

@app.route('/manager/saved-cutting-sheets')
def saved_cutting_sheets():
    if not session.get('role'):
        return redirect(url_for('index'))

    job_no = request.args.get('job_no') or request.args.get('order_id') or request.args.get('auto_job')
    order = Order.query.filter_by(job_no=job_no).first() if job_no else None
    cutting_sheets = CuttingSheet.query.filter_by(order_id=job_no).order_by(CuttingSheet.id.desc()).all() if job_no else []
    transfer_states = {}
    if order:
        sequence = CuttingSheet.query.filter_by(order_id=job_no).all()
        for sheet in cutting_sheets:
            transfer_states[sheet.id] = get_cutting_transfer_state(order, sheet, sequence)
    transfer_origins = {}
    if cutting_sheets:
        transfer_origins = {
            transfer.source_cutting_sheet_id: transfer
            for transfer in CuttingTransfer.query.filter(
                CuttingTransfer.source_cutting_sheet_id.in_([sheet.id for sheet in cutting_sheets])
            ).all()
        }
    article_filters = get_linked_article_order_filters(order) if order else []
    destination_orders = (
        Order.query.filter(Order.id != order.id, or_(*article_filters)).order_by(Order.id.desc()).all()
        if order and article_filters else []
    )
    if order:
        destination_orders.sort(key=lambda candidate: (candidate.id <= order.id, -candidate.id))
    return render_template(
        'saved_cutting_sheets.html',
        selected_job=job_no,
        order=order,
        cutting_sheets=cutting_sheets,
        transfer_states=transfer_states,
        transfer_origins=transfer_origins,
        destination_orders=destination_orders,
    )


@app.route('/manager/bundle-stickers/<int:cutting_sheet_id>', methods=['GET', 'POST'])
def bundle_stickers(cutting_sheet_id):
    if not session.get('role'):
        return redirect(url_for('index'))

    cutting_sheet = CuttingSheet.query.get_or_404(cutting_sheet_id)
    order = Order.query.filter_by(job_no=cutting_sheet.order_id).first()
    bundle_count_value = parse_numeric(cutting_sheet.bundle)
    bundle_count = (
        int(bundle_count_value)
        if bundle_count_value > 0 and bundle_count_value.is_integer()
        else 0
    )
    existing_entries = BundleStickerEntry.query.filter_by(
        cutting_sheet_id=cutting_sheet.id
    ).all()
    entries_by_number = {entry.bundle_number: entry for entry in existing_entries}
    submitted_pcs = {}

    if request.method == 'POST':
        if is_read_only_profile():
            return reject_read_only_edit()
        if bundle_count <= 0:
            flash('Enter a whole number of bundles on the cutting sheet before recording bundle PCS.', 'danger')
        else:
            pcs_by_bundle = {}
            invalid_bundles = []
            for bundle_number in range(1, bundle_count + 1):
                raw_pcs = (request.form.get(f'pcs_{bundle_number}') or '').strip()
                submitted_pcs[bundle_number] = raw_pcs
                try:
                    pcs = int(raw_pcs)
                except (TypeError, ValueError):
                    pcs = 0
                if pcs <= 0 or not raw_pcs.isdecimal():
                    invalid_bundles.append(bundle_number)
                else:
                    pcs_by_bundle[bundle_number] = pcs

            if invalid_bundles:
                flash('Enter a positive whole PCS count for every bundle.', 'danger')
            else:
                for bundle_number, pcs in pcs_by_bundle.items():
                    entry = entries_by_number.get(bundle_number)
                    if entry:
                        entry.pcs = pcs
                    else:
                        db.session.add(BundleStickerEntry(
                            cutting_sheet_id=cutting_sheet.id,
                            bundle_number=bundle_number,
                            pcs=pcs,
                        ))
                for entry in existing_entries:
                    if entry.bundle_number > bundle_count:
                        db.session.delete(entry)
                db.session.commit()
                flash('Bundle PCS saved successfully.', 'success')
                return redirect(url_for('bundle_stickers', cutting_sheet_id=cutting_sheet.id))

    return render_template(
        'bundle_stickers.html',
        cutting_sheet=cutting_sheet,
        order=order,
        bundle_count=bundle_count,
        entries_by_number=entries_by_number,
        submitted_pcs=submitted_pcs,
        read_only_profile=is_read_only_profile(),
    )


@app.route('/manager/cutting-transfer/destination-info')
def cutting_transfer_destination_info():
    if session.get('role') not in ('owner', 'manager'):
        return jsonify({'error': 'Unauthorized'}), 403

    source_sheet = CuttingSheet.query.get(request.args.get('source_sheet_id', type=int))
    destination_order = Order.query.get(request.args.get('destination_order_id', type=int))
    if not source_sheet or not destination_order or not destination_order.job_no:
        return jsonify({'error': 'The selected destination order is invalid.'}), 404
    if destination_order.job_no == source_sheet.order_id:
        return jsonify({'error': 'The source order cannot be selected as the destination.'}), 400
    source_order = Order.query.filter_by(job_no=source_sheet.order_id).first()
    if not source_order or not orders_share_article(source_order, destination_order):
        return jsonify({'error': 'Destination order must belong to the same article as the source order.'}), 400

    destination_sheets = CuttingSheet.query.filter_by(order_id=destination_order.job_no).all()
    return jsonify({
        'job_no': destination_order.job_no,
        'name': destination_order.name or '',
        'cut_count': len(destination_sheets),
        'cutting_pcs': sum(parse_numeric(sheet.quantity) for sheet in destination_sheets),
        'new_cut_no': get_next_cut_no_for_order(destination_order.job_no),
    })


@app.route('/manager/cutting-sheet/<int:source_sheet_id>/transfer-excess', methods=['POST'])
def transfer_excess_cutting_pcs(source_sheet_id):
    if session.get('role') not in ('owner', 'manager'):
        return jsonify({'error': 'Unauthorized'}), 403

    data = request.get_json(silent=True) or {}
    quantity_text = str(data.get('quantity', '')).strip()
    if not re.fullmatch(r'[0-9]+', quantity_text):
        return jsonify({'error': 'Transfer PCS must be a positive whole number.'}), 400
    quantity = int(quantity_text)
    if quantity <= 0:
        return jsonify({'error': 'Transfer PCS must be greater than 0.'}), 400

    source_sheet = CuttingSheet.query.get(source_sheet_id)
    if not source_sheet:
        return jsonify({'error': 'This cutting sheet no longer exists.'}), 404
    source_order = Order.query.filter_by(job_no=source_sheet.order_id).first()
    if not source_order:
        return jsonify({'error': 'The source order for this cutting sheet was not found.'}), 404

    destination_order_id = data.get('destination_order_id')
    if not str(destination_order_id or '').isdecimal():
        return jsonify({'error': 'Please select a destination order.'}), 400
    destination_order = Order.query.get(int(destination_order_id))
    if not destination_order or not destination_order.job_no:
        return jsonify({'error': 'The selected destination order is invalid.'}), 400
    if destination_order.job_no == source_order.job_no:
        return jsonify({'error': 'The source order cannot be selected as the destination.'}), 400
    if not orders_share_article(source_order, destination_order):
        return jsonify({'error': 'Destination order must belong to the same article as the source order.'}), 400

    try:
        # No-op updates acquire write locks on SQLite and row locks on PostgreSQL.
        db.session.query(CuttingSheet).filter_by(id=source_sheet.id).update(
            {CuttingSheet.quantity: CuttingSheet.quantity}, synchronize_session=False
        )
        db.session.query(Order).filter_by(id=destination_order.id).update(
            {Order.job_no: Order.job_no}, synchronize_session=False
        )
        db.session.expire(source_sheet)
        db.session.expire(destination_order)

        state = get_cutting_transfer_state(source_order, source_sheet)
        if state['remaining_transferable'] <= 0:
            db.session.rollback()
            return jsonify({'error': 'This cutting sheet no longer has transferable PCS.'}), 400
        if quantity > state['remaining_transferable']:
            maximum = state['remaining_transferable']
            db.session.rollback()
            return jsonify({
                'error': f'You can transfer a maximum of {maximum} PCS from this cut.'
            }), 400

        next_cut_no = get_next_cut_no_for_order(destination_order.job_no)
        destination_sheet = CuttingSheet(
            order_id=destination_order.job_no,
            cut_no=next_cut_no,
            serial_no=generate_cutting_sheet_serial(),
            quantity=str(quantity),
            total_cutting=str(quantity),
            total_pcs=str(quantity),
            summary_total_pcs=str(quantity),
            cut_date=datetime.utcnow().strftime('%Y-%m-%d'),
            remarks=f'{quantity} CUTTING PCS TRANSFERRED FROM {source_order.job_no} / Cut {source_sheet.cut_no}.',
        )
        db.session.add(destination_sheet)
        db.session.flush()
        transfer = CuttingTransfer(
            source_order_id=source_order.id,
            source_cutting_sheet_id=source_sheet.id,
            source_job_no=source_order.job_no,
            source_cut_no=source_sheet.cut_no,
            destination_order_id=destination_order.id,
            destination_cutting_sheet_id=destination_sheet.id,
            destination_job_no=destination_order.job_no,
            destination_cut_no=destination_sheet.cut_no,
            quantity=quantity,
            notes=f'Transferred from {source_order.job_no} / Cut {source_sheet.cut_no}.',
            created_by=session.get('name') or session.get('user') or '',
        )
        db.session.add(transfer)
        db.session.commit()
    except Exception:
        db.session.rollback()
        app.logger.exception('Unable to transfer excess cutting PCS')
        return jsonify({'error': 'The transfer could not be completed. Please try again.'}), 500

    updated_state = get_cutting_transfer_state(source_order, source_sheet)
    history = [{
        'quantity': item.quantity,
        'destination_order_id': item.destination_job_no,
        'destination_cut_no': item.destination_cutting_sheet.cut_no,
        'created_at': item.created_at.strftime('%Y-%m-%d %H:%M') if item.created_at else '',
        'created_by': item.created_by or '',
    } for item in updated_state['transfers']]
    return jsonify({
        'success': True,
        'quantity': quantity,
        'source_order_id': source_order.job_no,
        'source_cut_no': source_sheet.cut_no,
        'destination_order_id': destination_order.job_no,
        'destination_cut_no': destination_sheet.cut_no,
        'state': {
            'cutting_pcs': updated_state['cutting_pcs'],
            'required_portion': updated_state['required_portion'],
            'excess_pcs': updated_state['excess_pcs'],
            'transferred_pcs': updated_state['transferred_pcs'],
            'remaining_transferable': updated_state['remaining_transferable'],
            'transfers': history,
        },
    })

@app.route('/manager/delete-cutting-sheet', methods=['POST'])
def delete_cutting_sheet():
    if not session.get('role'):
        return redirect(url_for('index'))

    cutting_sheet_id = request.form.get('cutting_sheet_id')
    job_no = request.form.get('job_no', '')
    cutting_sheet = CuttingSheet.query.get(cutting_sheet_id) if cutting_sheet_id else None

    if cutting_sheet:
        if CuttingTransfer.query.filter(
            or_(
                CuttingTransfer.source_cutting_sheet_id == cutting_sheet.id,
                CuttingTransfer.destination_cutting_sheet_id == cutting_sheet.id,
            )
        ).first():
            flash('This cutting sheet has transfer history and cannot be deleted.', 'danger')
            return redirect(url_for('saved_cutting_sheets', job_no=job_no))

        deleted_logs = ProductionLog.query.filter_by(
            job_no=cutting_sheet.order_id,
            cut_no=cutting_sheet.cut_no
        ).delete(synchronize_session=False)

        inventory_serials = split_inventory_serials(cutting_sheet.inventory_serial_no)
        if inventory_serials:
            related_inventory_ids = [
                inv.id for inv in Inventory.query.filter(Inventory.serial_no.in_(inventory_serials)).all()
            ]
            if related_inventory_ids:
                InventoryRow.query.filter(
                    InventoryRow.inventory_id.in_(related_inventory_ids),
                    InventoryRow.sno == cutting_sheet.serial_no,
                    InventoryRow.cut_no == cutting_sheet.cut_no,
                ).delete(synchronize_session=False)

        db.session.delete(cutting_sheet)
        db.session.commit()
        flash(
            f'Cutting sheet deleted successfully. {deleted_logs} production log(s) removed.',
            'success'
        )
    else:
        flash('Cutting sheet not found.', 'danger')

    return redirect(url_for('saved_cutting_sheets', job_no=job_no))


@app.route('/manager/inventory-by-serial')
def inventory_by_serial():
    if not session.get('role'):
        return jsonify({"error": "Unauthorized"}), 403

    serial_no = (request.args.get('serial_no') or '').strip()
    if not serial_no:
        return jsonify({"error": "serial_no required"}), 400

    inventory = Inventory.query.filter_by(serial_no=serial_no).first()
    if not inventory:
        return jsonify({"error": "Inventory not found"}), 404

    try:
        requested_cut_no = int(str(request.args.get('cut_no') or '0'))
    except (TypeError, ValueError):
        requested_cut_no = 0
    total = parse_numeric(inventory.fabric_qty_a)
    if inventory_b_active_for_cut(inventory, requested_cut_no, request.args.get('order_id')):
        total += parse_numeric(inventory.fabric_qty_b)
    return jsonify({
        "serial_no": inventory.serial_no,
        "challan_no": inventory.challan_no or '',
        "fabric_qty_a": inventory.fabric_qty_a or '',
        "fabric_qty_b": inventory.fabric_qty_b or '',
        "fabric_meter_total": total
    })

@app.route('/manager/inventory')
def inventory():
    if not session.get('role'): return redirect(url_for('index'))
    job_no = request.args.get('job_no') or request.args.get('order_id')
    inv_id = request.args.get('inv_id') or request.args.get('inventory_id')
    order = Order.query.filter_by(job_no=job_no).first() if job_no else None

    inventory = None
    rows = []
    second_rows = []
    row_order_numbers = {}
    if inv_id:
        inventory = Inventory.query.get(inv_id)
        if inventory:
            serial_no = inventory.serial_no
            rows = sorted(inventory.rows, key=lambda row: row.id or 0)
            second_rows = sorted(inventory.second_rows, key=lambda r: r.idx) if getattr(inventory, 'second_rows', None) else []
        else:
            serial_no = request.args.get('serial_no') or generate_inventory_serial()
    else:
        serial_no = request.args.get('serial_no') or generate_inventory_serial()

        existing_inventory = Inventory.query.filter_by(serial_no=serial_no).first() if serial_no else None
        if existing_inventory:
            inventory = existing_inventory
            rows = sorted(existing_inventory.rows, key=lambda row: row.id or 0)
            second_rows = sorted(existing_inventory.second_rows, key=lambda r: r.idx) if getattr(existing_inventory, 'second_rows', None) else []
        else:
            challan = ReceivingChallan.query.filter_by(serial_no=serial_no).first() if serial_no else None
            if challan:
                inventory = build_inventory_prefill_from_challan(challan, serial_no)

    if inventory:
        inventory.total = f'{calculate_inventory_received_total(inventory):.2f}'
        if inventory.serial_no and inventory.id:
            inventory_order = Order.query.filter_by(job_no=inventory.order_id).first()
            article_order_ids = {inventory.order_id}
            if inventory_order:
                article_order_ids.update(get_article_order_numbers(inventory_order.job_no))
            related_sheets = CuttingSheet.query.filter(
                CuttingSheet.order_id.in_(article_order_ids)
            ).order_by(CuttingSheet.id.asc()).all()
            row_order_numbers = {
                (sheet.serial_no, sheet.cut_no): sheet.order_id
                for sheet in related_sheets
            }
            cutting_sheets_by_serial_cut = {
                (sheet.serial_no, str(sheet.cut_no)): sheet
                for sheet in related_sheets
            }
            shortage_totals_by_sheet = {}
            cutting_sheet_ids = [sheet.id for sheet in related_sheets if sheet.id]
            if cutting_sheet_ids:
                for cutting_row in CuttingSheetRow.query.filter(
                    CuttingSheetRow.cutting_sheet_id.in_(cutting_sheet_ids),
                    CuttingSheetRow.idx >= 1,
                    CuttingSheetRow.idx <= 19,
                ).all():
                    if (cutting_row.cp or '').strip():
                        shortage_totals_by_sheet[cutting_row.cutting_sheet_id] = (
                            shortage_totals_by_sheet.get(cutting_row.cutting_sheet_id, 0.0)
                            + parse_numeric(cutting_row.cp)
                        )
            inventory_total = calculate_inventory_received_total(inventory)
            running_balance = inventory_total
            for sheet in related_sheets:
                if inventory.serial_no not in split_inventory_serials(sheet.inventory_serial_no):
                    continue
                sheet_order = Order.query.filter_by(job_no=sheet.order_id).first()
                sheet_file_no = (sheet_order.file_no if sheet_order else '') or ''
                mirrored_row = InventoryRow.query.filter_by(
                    inventory_id=inventory.id,
                    sno=sheet.serial_no,
                    cut_no=sheet.cut_no,
                ).first()
                if mirrored_row:
                    running_balance -= parse_numeric(mirrored_row.fabric_use)
                    mirrored_row.balance = f'{running_balance:.2f}'
                    if sheet_file_no:
                        mirrored_row.file_no = sheet_file_no
            db.session.commit()
            for row in rows:
                order_number = row_order_numbers.get((row.sno, row.cut_no), '')
                order_match = re.search(r'(\d+)$', str(order_number))
                row.order_no = order_match.group(1) if order_match else order_number
                cutting_sheet = cutting_sheets_by_serial_cut.get((row.sno, str(row.cut_no)))
                shortage_total = shortage_totals_by_sheet.get(cutting_sheet.id) if cutting_sheet else None
                row.shortage_total = (
                    f'{shortage_total:.2f}'.rstrip('0').rstrip('.')
                    if shortage_total is not None else ''
                )
        fabric_status = calculate_inventory_fabric_balances(inventory)
        actual_used = calculate_inventory_actual_used_fabric(inventory)
        inventory.used_fabric = f"{actual_used:.2f}"
        inventory.left_over_fabric = f"{max(0.0, fabric_status['left_over_fabric']):.2f}"
        inventory.rejected_fabric = f"{fabric_status['rejected_fabric'] + fabric_status['recovered_fabric']:.2f}"

    total_cutting_pcs = sum(
        int(parse_numeric(row.cutting_pcs))
        for row in rows
        if row.cutting_pcs is not None
    )
    total_fabric_use = sum(parse_numeric(row.fabric_use) for row in rows if row.fabric_use is not None)
    total_shortage = sum(
        parse_numeric(row.shortage_total)
        for row in rows
        if row.shortage_total not in (None, '')
    )
    total_cut_pcs = sum(
        int(parse_numeric(row.cut_pcs))
        for row in rows
        if row.cut_pcs is not None
    )
    total_wastage = sum(parse_numeric(row.wastage) for row in rows if row.wastage is not None)
    inventory_has_cutting_data = bool(rows)
    summary_item = next((row.item for row in rows if row.item), '')
    summary_cut_size = next((row.cut_size for row in rows if row.cut_size), '')
    remaining_a_quality = calculate_inventory_consumption_state(inventory, order_id=job_no)['a_remaining']
    remaining_b_quality = calculate_inventory_b_quality_remaining(inventory)
    fabric_balance_before_b = ''
    remaining_fabric_balance = ''
    row_4 = next((row for row in second_rows if getattr(row, 'idx', None) == 4), None)
    b_quality_applied = bool(inventory and getattr(inventory, 'fabric_b_enabled', False))
    numeric_balance_rows = [row for row in rows if row.balance not in (None, '')]
    if numeric_balance_rows:
        latest_balance_row = max(numeric_balance_rows, key=lambda row: row.id or 0)
        fabric_balance_before_b = f'{parse_numeric(latest_balance_row.balance):.2f}'
    if fabric_balance_before_b:
        balance_after_b = parse_numeric(fabric_balance_before_b)
        if b_quality_applied:
            balance_after_b = remaining_b_quality
        remaining_fabric_balance = f'{max(0.0, balance_after_b):.2f}'
    fabric_balance_status = ''
    if remaining_fabric_balance and b_quality_applied:
        fabric_balance_status = 'COMPLETED' if parse_numeric(remaining_fabric_balance) == 0 else 'NOT COMPLETED'
    inventory_status = get_inventory_status(inventory) if inventory else 'NOT USED'
    return render_template(
        'inventory.html',
        selected_job=job_no,
        order=order,
        serial_no=serial_no,
        inventory=inventory,
        inventory_status=inventory_status,
        rows=rows,
        second_rows=second_rows,
        total_cutting_pcs=total_cutting_pcs,
        total_fabric_use=total_fabric_use,
        total_shortage=total_shortage,
        total_cut_pcs=total_cut_pcs,
        total_wastage=total_wastage,
        inventory_has_cutting_data=inventory_has_cutting_data,
        summary_item=summary_item,
        summary_cut_size=summary_cut_size,
        fabric_balance_before_b=fabric_balance_before_b,
        remaining_fabric_balance=remaining_fabric_balance,
        fabric_balance_status=fabric_balance_status,
        remaining_a_quality=remaining_a_quality,
        b_quality_applied=b_quality_applied,
        remaining_b_quality=remaining_b_quality,
    )

@app.route('/manager/save-inventory', methods=['POST'])
def save_inventory():
    if not session.get('role'):
        return redirect(url_for('index'))

    job_no = request.args.get('job_no') or request.form.get('job_no') or request.args.get('order_id') or request.args.get('auto_job') or ''
    order = Order.query.filter_by(job_no=job_no).first() if job_no else None
    inventory_id = request.form.get('inventory_id') or request.args.get('inv_id')
    if inventory_id and (
        session.get('role') not in ('owner', 'manager') or is_read_only_profile()
    ):
        return reject_read_only_edit('Only the owner and manager can update saved inventory records.')
    serial_no = request.form.get('serial_no') or request.args.get('serial_no') or generate_inventory_serial()

    required_header_keys = [
        'recv_date', 'suppliers', 'received_from', 'challan_no', 'place', 'meter_note', 'file_no',
        'fabric_quality', 'cut_size_header', 'width', 'req_cutting', 'fabric_for', 'consumption', 'req_average'
    ]
    form_headers = {k: request.form.get(k, '').strip() for k in required_header_keys}

    inventory_entry = None
    if inventory_id:
        try:
            inv_id_int = int(inventory_id)
        except Exception:
            inv_id_int = None

        if inv_id_int is not None:
            inventory_entry = Inventory.query.get(inv_id_int)
        if inventory_entry is None and inv_id_int is not None:
            flash('Inventory record not found; creating a new record instead.', 'warning')

    supplier_value = request.form.get('suppliers', '')
    received_from_value = request.form.get('received_from', '')

    fabric_a_value = parse_numeric(request.form.get('fabric_qty_a', ''))
    total_value = sum(
        parse_numeric(request.form.get(field, ''))
        for field in ('fabric_qty_a', 'fabric_qty_b', 'receive_cut_pcs')
    )
    used_value = min(calculate_inventory_used_fabric(serial_no, job_no), total_value)
    rejected_value = max(0.0, parse_numeric(request.form.get('rejected_fabric', '')))

    if inventory_entry:
        original_rejected_pool = (
            max(0.0, parse_numeric(getattr(inventory_entry, 'rejected_fabric', 0)))
            + max(0.0, parse_numeric(getattr(inventory_entry, 'rejected_recovered_fabric', 0)))
        )
    else:
        original_rejected_pool = rejected_value
    enable_fabric_b = request.form.get('enable_fabric_b') == 'on'
    was_fabric_b_enabled = bool(inventory_entry and getattr(inventory_entry, 'fabric_b_enabled', False))
    has_activation_order = bool(inventory_entry and getattr(inventory_entry, 'fabric_b_activation_order_id', None))
    if enable_fabric_b and (not was_fabric_b_enabled or not has_activation_order):
        existing_cut_numbers = []
        if inventory_entry:
            for sheet in CuttingSheet.query.filter_by(order_id=inventory_entry.order_id).all():
                if inventory_entry.serial_no not in split_inventory_serials(sheet.inventory_serial_no):
                    continue
                try:
                    existing_cut_numbers.append(int(str(sheet.cut_no)))
                except (TypeError, ValueError):
                    continue
        activation_cut_no = max(existing_cut_numbers, default=0) + 1
    else:
        activation_cut_no = getattr(inventory_entry, 'fabric_b_activation_cut_no', None) if inventory_entry else None
    b_used_after_activation = False
    if inventory_entry and was_fabric_b_enabled and not enable_fabric_b and activation_cut_no is not None:
        b_used_after_activation = any(
            str(getattr(row, 'cut_no', '')).strip().isdigit()
            and int(str(row.cut_no)) >= int(activation_cut_no)
            and parse_numeric(row.fabric_use) > 0
            for row in InventoryRow.query.filter_by(inventory_id=inventory_entry.id).all()
        )
    fabric_b_enabled_for_save = enable_fabric_b or (was_fabric_b_enabled and b_used_after_activation)
    if fabric_b_enabled_for_save:
        used_value = min(
            calculate_inventory_used_fabric(serial_no, job_no),
            fabric_a_value + parse_numeric(request.form.get('fabric_qty_b', '')),
        )
    reactive_value = min(
        max(0.0, parse_numeric(request.form.get('re_active_fabric', ''))),
        original_rejected_pool,
    )
    updated_rejected_value = max(0.0, rejected_value - reactive_value)
    left_over_value = max(
        0.0,
        fabric_a_value - used_value - updated_rejected_value + reactive_value,
    )
    if fabric_b_enabled_for_save:
        left_over_value = max(
            0.0,
            fabric_a_value
            + parse_numeric(request.form.get('fabric_qty_b', ''))
            - used_value
            - updated_rejected_value
            + reactive_value,
        )

    normalized_challan_no = normalize_challan_number(request.form.get('challan_no', ''))

    if inventory_entry:
        inventory_entry.recv_date = request.form.get('recv_date', '')
        inventory_entry.received_from = received_from_value
        inventory_entry.suppliers = supplier_value
        inventory_entry.challan_no = normalized_challan_no
        inventory_entry.place = request.form.get('place', '')
        inventory_entry.meter_note = request.form.get('meter_note', '')
        inventory_entry.ms = request.form.get('ms', '')
        inventory_entry.file_no = request.form.get('file_no', '')
        inventory_entry.fabric_qty_a = request.form.get('fabric_qty_a', '')
        inventory_entry.fabric_qty_b = request.form.get('fabric_qty_b', '')
        inventory_entry.fabric_b_enabled = fabric_b_enabled_for_save
        inventory_entry.fabric_b_activation_cut_no = activation_cut_no if fabric_b_enabled_for_save else None
        if enable_fabric_b and (not was_fabric_b_enabled or not getattr(inventory_entry, 'fabric_b_activation_order_id', None)):
            inventory_entry.fabric_b_activation_order_id = inventory_entry.order_id
        elif not fabric_b_enabled_for_save:
            inventory_entry.fabric_b_activation_order_id = None
        inventory_entry.fabric_quality = request.form.get('fabric_quality', '')
        inventory_entry.cut_size_header = request.form.get('cut_size_header', '')
        inventory_entry.width = request.form.get('width', '')
        inventory_entry.req_cutting = request.form.get('req_cutting', '')
        inventory_entry.receive_cut_pcs = request.form.get('receive_cut_pcs', '')
        inventory_entry.fabric_for = request.form.get('fabric_for', '')
        inventory_entry.consumption = request.form.get('consumption', '')
        inventory_entry.req_average = request.form.get('req_average', '')
        inventory_entry.total = f'{total_value:.2f}'
        inventory_entry.used_fabric = f'{used_value:.2f}'
        inventory_entry.left_over_fabric = f'{left_over_value:.2f}'
        inventory_entry.rejected_fabric = f'{updated_rejected_value:.2f}'
        inventory_entry.rejected_recovered_fabric = f'{reactive_value:.2f}'
        inventory_entry.serial_no = serial_no
    else:
        inventory_entry = Inventory(
            serial_no=serial_no,
            order_id=job_no,
            recv_date=request.form.get('recv_date', ''),
            received_from=received_from_value,
            suppliers=supplier_value,
            challan_no=normalized_challan_no,
            place=request.form.get('place', ''),
            meter_note=request.form.get('meter_note', ''),
            ms=request.form.get('ms', ''),
            file_no=request.form.get('file_no', ''),
            fabric_qty_a=request.form.get('fabric_qty_a', ''),
            fabric_qty_b=request.form.get('fabric_qty_b', ''),
            fabric_b_enabled=fabric_b_enabled_for_save,
            fabric_b_activation_cut_no=activation_cut_no if fabric_b_enabled_for_save else None,
            fabric_b_activation_order_id=job_no if fabric_b_enabled_for_save else None,
            fabric_quality=request.form.get('fabric_quality', ''),
            cut_size_header=request.form.get('cut_size_header', ''),
            width=request.form.get('width', ''),
            req_cutting=request.form.get('req_cutting', ''),
            receive_cut_pcs=request.form.get('receive_cut_pcs', ''),
            fabric_for=request.form.get('fabric_for', ''),
            consumption=request.form.get('consumption', ''),
            req_average=request.form.get('req_average', ''),
            total=f'{total_value:.2f}',
            used_fabric=f'{used_value:.2f}',
            left_over_fabric=f'{left_over_value:.2f}',
            rejected_fabric=f'{updated_rejected_value:.2f}',
            rejected_recovered_fabric=f'{reactive_value:.2f}'
        )
        db.session.add(inventory_entry)

    missing = [k for k, v in form_headers.items() if not v]
    if missing:
        rows = []
        for i in range(1, 15):
            rdate = request.form.get(f'date_{i}', '').strip()
            ritem = request.form.get(f'item_{i}', '').strip()
            rsno = request.form.get(f'sno_{i}', '').strip()
            rfile = request.form.get(f'file_{i}', '').strip()
            rcut_no = request.form.get(f'cut_no_{i}', '').strip()
            rcut_size = request.form.get(f'cut_size_{i}', '').strip()
            rcutting_pcs = request.form.get(f'cutting_pcs_{i}', '').strip()
            rfabric_req = request.form.get(f'fabric_req_{i}', '').strip()
            rfabric_issue = request.form.get(f'fabric_issue_{i}', '').strip()
            rissue_by = request.form.get(f'issue_by_{i}', '').strip()
            rfabric_return = request.form.get(f'fabric_return_{i}', '').strip()
            rfabric_use = request.form.get(f'fabric_use_{i}', '').strip()
            rwastage = request.form.get(f'wastage_{i}', '').strip()
            rcut_pcs = request.form.get(f'cut_pcs_{i}', '').strip()
            rbalance = request.form.get(f'balance_{i}', '').strip()

            if any([rdate, ritem, rsno, rfile, rcut_no, rcut_size, rcutting_pcs, rfabric_req, rfabric_issue, rissue_by, rfabric_return, rfabric_use, rwastage, rcut_pcs, rbalance]):
                rows.append(SimpleNamespace(
                    idx=i,
                    date=rdate or None,
                    item=ritem or None,
                    sno=rsno or None,
                    file_no=rfile or None,
                    cut_no=rcut_no or None,
                    cut_size=rcut_size or None,
                    cutting_pcs=(int(rcutting_pcs) if rcutting_pcs.replace('.', '', 1).isdigit() else None) if rcutting_pcs else None,
                    fabric_req=rfabric_req or None,
                    fabric_issue=rfabric_issue or None,
                    issue_by=rissue_by or None,
                    fabric_return=rfabric_return or None,
                    fabric_use=rfabric_use or None,
                    wastage=rwastage or None,
                    cut_pcs=(int(rcut_pcs) if rcut_pcs.replace('.', '', 1).isdigit() else None) if rcut_pcs else None,
                    balance=rbalance or None
                ))

        second_rows = []
        for i in range(1, 6):
            style = request.form.get(f'sec_style_{i}', '').strip()
            sno = request.form.get(f'sec_sno_{i}', '').strip()
            cut_size = request.form.get(f'sec_cut_size_{i}', '').strip()
            cutting_pcs = request.form.get(f'sec_cutting_pcs_{i}', '').strip()
            fabric_use = request.form.get(f'sec_fabric_use_{i}', '').strip()
            cut_pcs = request.form.get(f'sec_cut_pcs_{i}', '').strip()
            shortage = request.form.get(f'sec_shortage_{i}', '').strip()
            balance = request.form.get(f'sec_balance_{i}', '').strip()

            if any([style, sno, cut_size, cutting_pcs, fabric_use, cut_pcs, shortage, balance]):
                second_rows.append(SimpleNamespace(
                    idx=i,
                    style=style or None,
                    sno=sno or None,
                    cut_size=cut_size or None,
                    cutting_pcs=(int(float(cutting_pcs)) if cutting_pcs.replace('.', '', 1).isdigit() else None) if cutting_pcs else None,
                    fabric_use=fabric_use or None,
                    cut_pcs=(int(float(cut_pcs)) if cut_pcs.replace('.', '', 1).isdigit() else None) if cut_pcs else None,
                    shortage=shortage or None,
                    balance=balance or None
                ))

        inv_obj = SimpleNamespace(**{k: v for k, v in form_headers.items()})
        inv_obj.serial_no = serial_no
        inv_obj.id = inventory_entry.id if inventory_entry and getattr(inventory_entry, 'id', None) else None
        db.session.rollback()
        flash('Please fill all required header fields before saving.', 'danger')
        return render_template('inventory.html', selected_job=job_no, order=order, serial_no=serial_no, inventory=inv_obj, inventory_status=get_inventory_status(inventory_entry), rows=rows, second_rows=second_rows, remaining_a_quality=calculate_inventory_consumption_state(inventory_entry, order_id=job_no)['a_remaining'])

    try:
        db.session.flush()

        submitted_shortage_4 = [
            (value or '').strip().upper()
            for value in request.form.getlist('sec_shortage_4')
            if (value or '').strip()
        ]
        submitted_shortage_4_flag = [
            (value or '').strip().upper()
            for value in request.form.getlist('sec_shortage_4_flag')
            if (value or '').strip()
        ]
        submitted_shortage_5 = [
            (value or '').strip().upper()
            for value in request.form.getlist('sec_shortage_5')
            if (value or '').strip()
        ]
        submitted_shortage_5_flag = [
            (value or '').strip().upper()
            for value in request.form.getlist('sec_shortage_5_flag')
            if (value or '').strip()
        ]
        a_return_already_recorded = bool(
            inventory_entry
            and (
                getattr(inventory_entry, 'a_returned_to_party', False)
                or parse_numeric(getattr(inventory_entry, 'a_returned_quantity', 0)) > 0
            )
        )
        b_return_already_recorded = bool(
            inventory_entry
            and (
                getattr(inventory_entry, 'b_returned_to_party', False)
                or parse_numeric(getattr(inventory_entry, 'b_returned_quantity', 0)) > 0
            )
        )
        selected_a_return = (
            'RETURNED' in submitted_shortage_4
            or 'RETURNED' in submitted_shortage_4_flag
            or a_return_already_recorded
        )
        selected_b_return = (
            'RETURNED' in submitted_shortage_5
            or 'RETURNED' in submitted_shortage_5_flag
            or b_return_already_recorded
        )

        if inventory_entry and selected_a_return and not a_return_already_recorded:
            remaining_return_qty = calculate_inventory_returnable_a_quantity(inventory_entry, order_id=job_no)
            current_return_quantity = max(0.0, parse_numeric(getattr(inventory_entry, 'fabric_qty_a', 0)))
            inventory_entry.fabric_qty_a = f'{max(0.0, current_return_quantity - remaining_return_qty):.2f}'
            if remaining_return_qty > 0:
                inventory_entry.a_returned_to_party = True
                inventory_entry.a_returned_date = datetime.utcnow().strftime('%Y-%m-%d')
                inventory_entry.a_returned_by = session.get('name') or session.get('user') or ''
                inventory_entry.a_returned_party = order.name if order else (received_from_value or '')
                inventory_entry.a_returned_article = (order.article_name or order.article or '') if order else (inventory_entry.fabric_for or '')
                inventory_entry.a_returned_quantity = f'{remaining_return_qty:.2f}'
            inventory_entry.left_over_fabric = f'{max(0.0, parse_numeric(inventory_entry.fabric_qty_a) + max(0.0, parse_numeric(inventory_entry.fabric_qty_b)) - max(0.0, parse_numeric(inventory_entry.used_fabric)) - max(0.0, parse_numeric(inventory_entry.rejected_fabric))):.2f}'

        if inventory_entry and selected_b_return and not b_return_already_recorded:
            remaining_return_qty = calculate_inventory_returnable_b_quantity(inventory_entry, order_id=job_no)
            current_return_quantity = max(0.0, parse_numeric(getattr(inventory_entry, 'fabric_qty_b', 0)))
            inventory_entry.fabric_qty_b = f'{max(0.0, current_return_quantity - remaining_return_qty):.2f}'
            inventory_entry.fabric_b_enabled = False
            if remaining_return_qty > 0:
                inventory_entry.b_returned_to_party = True
                inventory_entry.b_returned_date = datetime.utcnow().strftime('%Y-%m-%d')
                inventory_entry.b_returned_by = session.get('name') or session.get('user') or ''
                inventory_entry.b_returned_party = order.name if order else (received_from_value or '')
                inventory_entry.b_returned_article = (order.article_name or order.article or '') if order else (inventory_entry.fabric_for or '')
                inventory_entry.b_returned_quantity = f'{remaining_return_qty:.2f}'
            inventory_entry.left_over_fabric = f'{max(0.0, parse_numeric(inventory_entry.fabric_qty_a) + max(0.0, parse_numeric(inventory_entry.fabric_qty_b)) - max(0.0, parse_numeric(inventory_entry.used_fabric)) - max(0.0, parse_numeric(inventory_entry.rejected_fabric))):.2f}'

        if inventory_entry.id:
            InventoryRow.query.filter_by(inventory_id=inventory_entry.id).delete()
            InventorySecondRow.query.filter_by(inventory_id=inventory_entry.id).delete()

        for i in range(1, 15):
            date_val = request.form.get(f'date_{i}', '').strip()
            item_val = request.form.get(f'item_{i}', '').strip()
            sno_val = request.form.get(f'sno_{i}', '').strip()
            file_val = request.form.get(f'file_{i}', '').strip()
            cut_no_val = request.form.get(f'cut_no_{i}', '').strip()
            cut_size_val = request.form.get(f'cut_size_{i}', '').strip()
            cutting_pcs_val = request.form.get(f'cutting_pcs_{i}', '').strip()
            fabric_req_val = request.form.get(f'fabric_req_{i}', '').strip()
            fabric_issue_val = request.form.get(f'fabric_issue_{i}', '').strip()
            issue_by_val = request.form.get(f'issue_by_{i}', '').strip()
            fabric_return_val = request.form.get(f'fabric_return_{i}', '').strip()
            fabric_use_val = request.form.get(f'fabric_use_{i}', '').strip()
            wastage_val = request.form.get(f'wastage_{i}', '').strip()
            cut_pcs_val = request.form.get(f'cut_pcs_{i}', '').strip()
            balance_val = request.form.get(f'balance_{i}', '').strip()

            if any([date_val, item_val, sno_val, file_val, cut_no_val, cut_size_val, cutting_pcs_val, fabric_req_val, fabric_issue_val, issue_by_val, fabric_return_val, fabric_use_val, wastage_val, cut_pcs_val, balance_val]):
                row = InventoryRow(
                    inventory_id=inventory_entry.id,
                    idx=i,
                    date=date_val or None,
                    item=item_val or None,
                    sno=sno_val or None,
                    file_no=file_val or None,
                    cut_no=cut_no_val or None,
                    cut_size=cut_size_val or None,
                    cutting_pcs=int(float(cutting_pcs_val)) if cutting_pcs_val.replace('.', '', 1).isdigit() else None,
                    fabric_req=fabric_req_val or None,
                    fabric_issue=fabric_issue_val or None,
                    issue_by=issue_by_val or None,
                    fabric_return=fabric_return_val or None,
                    fabric_use=fabric_use_val or None,
                    wastage=wastage_val or None,
                    cut_pcs=int(float(cut_pcs_val)) if cut_pcs_val.replace('.', '', 1).isdigit() else None,
                    balance=balance_val or None
                )
                db.session.add(row)

        for i in range(1, 6):
            style_val = request.form.get(f'sec_style_{i}', '').strip()
            sno_val = request.form.get(f'sec_sno_{i}', '').strip()
            cut_size_val = request.form.get(f'sec_cut_size_{i}', '').strip()
            cutting_pcs_val = request.form.get(f'sec_cutting_pcs_{i}', '').strip()
            fabric_use_val = request.form.get(f'sec_fabric_use_{i}', '').strip()
            cut_pcs_val = request.form.get(f'sec_cut_pcs_{i}', '').strip()
            shortage_val = request.form.get(f'sec_shortage_{i}', '').strip()
            balance_val = request.form.get(f'sec_balance_{i}', '').strip()

            if any([style_val, sno_val, cut_size_val, cutting_pcs_val, fabric_use_val, cut_pcs_val, shortage_val, balance_val]):
                srow = InventorySecondRow(
                    inventory_id=inventory_entry.id,
                    idx=i,
                    style=style_val or None,
                    sno=sno_val or None,
                    cut_size=cut_size_val or None,
                    cutting_pcs=int(float(cutting_pcs_val)) if cutting_pcs_val.replace('.', '', 1).isdigit() else None,
                    fabric_use=fabric_use_val or None,
                    cut_pcs=int(float(cut_pcs_val)) if cut_pcs_val.replace('.', '', 1).isdigit() else None,
                    shortage=shortage_val or None,
                    balance=balance_val or None
                )
                db.session.add(srow)

        db.session.commit()
        next_serial, has_pending_inventory = get_next_pending_inventory_serial(job_no)
        if has_pending_inventory:
            flash(f'Inventory saved successfully. Next pending inventory is for serial {next_serial}.', 'success')
            return redirect(url_for('inventory', job_no=job_no, serial_no=next_serial))

        flash(f'Inventory saved successfully. Ready for next receiving challan entry with serial {next_serial}.', 'success')
        return redirect(url_for('receiving_challan', job_no=job_no, serial_no=next_serial))
    except Exception as e:
        db.session.rollback()
        flash(f'Unable to save inventory: {e}', 'danger')
        rows = []
        for i in range(1, 15):
            rdate = request.form.get(f'date_{i}', '').strip()
            ritem = request.form.get(f'item_{i}', '').strip()
            rsno = request.form.get(f'sno_{i}', '').strip()
            rfile = request.form.get(f'file_{i}', '').strip()
            rcut_no = request.form.get(f'cut_no_{i}', '').strip()
            rcut_size = request.form.get(f'cut_size_{i}', '').strip()
            rcutting_pcs = request.form.get(f'cutting_pcs_{i}', '').strip()
            rfabric_req = request.form.get(f'fabric_req_{i}', '').strip()
            rfabric_issue = request.form.get(f'fabric_issue_{i}', '').strip()
            rissue_by = request.form.get(f'issue_by_{i}', '').strip()
            rfabric_return = request.form.get(f'fabric_return_{i}', '').strip()
            rfabric_use = request.form.get(f'fabric_use_{i}', '').strip()
            rwastage = request.form.get(f'wastage_{i}', '').strip()
            rcut_pcs = request.form.get(f'cut_pcs_{i}', '').strip()
            rbalance = request.form.get(f'balance_{i}', '').strip()

            if any([rdate, ritem, rsno, rfile, rcut_no, rcut_size, rcutting_pcs, rfabric_req, rfabric_issue, rissue_by, rfabric_return, rfabric_use, rwastage, rcut_pcs, rbalance]):
                rows.append(SimpleNamespace(
                    idx=i,
                    date=rdate or None,
                    item=ritem or None,
                    sno=rsno or None,
                    file_no=rfile or None,
                    cut_no=rcut_no or None,
                    cut_size=rcut_size or None,
                    cutting_pcs=(int(rcutting_pcs) if rcutting_pcs.replace('.', '', 1).isdigit() else None) if rcutting_pcs else None,
                    fabric_req=rfabric_req or None,
                    fabric_issue=rfabric_issue or None,
                    issue_by=rissue_by or None,
                    fabric_return=rfabric_return or None,
                    fabric_use=rfabric_use or None,
                    wastage=rwastage or None,
                    cut_pcs=(int(rcut_pcs) if rcut_pcs.replace('.', '', 1).isdigit() else None) if rcut_pcs else None,
                    balance=rbalance or None
                ))

        inv_obj = SimpleNamespace(**{k: v for k, v in form_headers.items()})
        inv_obj.serial_no = serial_no
        inv_obj.id = inventory_entry.id if inventory_entry and getattr(inventory_entry, 'id', None) else None
        return render_template('inventory.html', selected_job=job_no, order=order, serial_no=serial_no, inventory=inv_obj, inventory_status=get_inventory_status(inventory_entry), rows=rows, remaining_a_quality=calculate_inventory_consumption_state(inventory_entry, order_id=job_no)['a_remaining'])


@app.route('/manager/saved-inventory')
def saved_inventory():
    if not session.get('role'): return redirect(url_for('index'))
    job_no = request.args.get('job_no') or request.args.get('order_id') or request.args.get('auto_job')
    article_order_numbers = get_article_order_numbers(job_no)
    inventories = (
        Inventory.query.filter(Inventory.order_id.in_(article_order_numbers))
        .order_by(Inventory.id.desc()).all()
        if article_order_numbers else []
    )
    inventory_statuses = {inventory.id: get_inventory_status(inventory) for inventory in inventories}
    return render_template('saved_inventory.html', order_id=job_no, Inventory=inventories, inventory_statuses=inventory_statuses)

@app.route('/manager/saved-requirements')
def saved_requirements():
    if not session.get('role'): return redirect(url_for('index'))
    order_id = request.args.get('order_id') or request.args.get('job_no') or request.args.get('auto_job')
    po_search = (request.args.get('po_search') or '').strip()
    base_query = SavedRequirement.query.filter_by(order_id=order_id) if order_id else None
    if base_query is None:
        requirements = []
    else:
        if po_search:
            # case-insensitive match on po_no
            requirements = base_query.filter(func.lower(SavedRequirement.po_no).like(f"%{po_search.lower()}%"))
            requirements = requirements.order_by(SavedRequirement.id.desc()).all()
        else:
            requirements = base_query.order_by(SavedRequirement.id.desc()).all()

    # Group by PO No (po_no). Preserve order of appearance by using list of tuples.
    grouped = {}
    order_of_pos = []
    for req in requirements:
        po = (req.po_no or '').strip() or 'UNASSIGNED'
        if po not in grouped:
            grouped[po] = []
            order_of_pos.append(po)
        grouped[po].append(req)

    # Build ordered list of (po_no, [requirements])
    grouped_requirements = [(po, grouped[po]) for po in order_of_pos]

    return render_template('saved_requirements.html', order_id=order_id, grouped_requirements=grouped_requirements, po_search=po_search)

@app.route('/manager/production_entry', methods=['GET', 'POST'])
def production_entry():
    if not session.get('role'): 
        return redirect(url_for('index'))

    prefill_job = (
        request.args.get('auto_job')
        or request.args.get('job_no')
        or request.args.get('order_id')
        or request.form.get('job_no')
    )
    selected_cut = request.args.get('cut_no')
    selected_operation = request.args.get('operation')
    
    # 1. Fetch the specific order if it exists
    order = Order.query.filter_by(job_no=prefill_job).first() if prefill_job else None
    if not order:
        flash('Order not found. Please open a valid order first.', 'danger')
        return redirect(url_for('manager_dashboard'))

    cutting_sheets = CuttingSheet.query.filter_by(order_id=prefill_job).all()
    cutting_sheets = sorted(
        cutting_sheets,
        key=lambda sheet: (
            int(str(sheet.cut_no)) if str(sheet.cut_no).isdigit() else 999999,
            sheet.id
        )
    )
    if not selected_cut and cutting_sheets:
        selected_cut = str(cutting_sheets[0].cut_no)

    article_for_rates = order.article_ref if order and order.article_ref else None
    if not article_for_rates and order and order.article:
        article_for_rates = Article.query.filter_by(article_no=normalize_article_no(order.article)).first()
    selected_rates = get_rates_for_order(order) if order else get_rates_for_article(article_for_rates)
    article_special_assignments = get_article_special_assignments(get_article_for_order(order))
    special_operation_ids = {item.rate_id for item in article_special_assignments}
    special_operations = OperationRate.query.filter(
        OperationRate.id.in_(special_operation_ids)
    ).order_by(OperationRate.operation.asc()).all() if special_operation_ids else []
    special_operation_names = {(rate.operation or '').upper() for rate in special_operations}
    special_operation_ids_by_name = {
        (rate.operation or '').upper(): rate.id for rate in special_operations
    }
    enabled_special_operation_ids_by_cut = {}
    for selection in CutSpecialOperation.query.filter_by(order_id=order.id).all():
        if selection.rate_id in special_operation_ids:
            enabled_special_operation_ids_by_cut.setdefault(str(selection.cut_no), []).append(selection.rate_id)
    resume_operations_by_cut = {}
    operation_limits_by_cut = {}
    for sheet in cutting_sheets:
        cut_limit = parse_numeric(sheet.quantity)
        if cut_limit <= 0:
            continue
        operation_names = list(get_rates_for_cut(order, sheet.cut_no).keys())
        if not operation_names:
            continue
        production_state = get_cut_production_state(
            prefill_job,
            sheet.cut_no,
            cut_limit,
            operation_names,
        )
        operation_limits_by_cut[str(sheet.cut_no)] = production_state['effective_limits']
        for operation_name in operation_names:
            completion_limit = production_state['effective_limits'].get(
                operation_name,
                production_state['limits_before_bq'].get(operation_name, 0),
            ) if production_state['machine_operations'].get(operation_name) else production_state['limits_before_bq'].get(operation_name, 0)
            if production_state['raw_totals'].get(operation_name, 0) < completion_limit:
                resume_operations_by_cut[str(sheet.cut_no)] = operation_name
                break

    if selected_cut:
        selected_rates = get_rates_for_cut(order, selected_cut)
    if selected_cut and selected_rates:
        selected_operation = resume_operations_by_cut.get(str(selected_cut))

    if request.method == 'POST':
        if request.form.get('save_cut_special_operations'):
            job_no = request.form.get('job_no')
            selected_cut = request.form.get('cut_no')
            try:
                if is_read_only_profile():
                    return reject_read_only_edit('This profile cannot change cut operation selections.')
                cut_sheet = CuttingSheet.query.filter_by(order_id=job_no, cut_no=selected_cut).first()
                if not cut_sheet:
                    raise ValueError('Selected cut number is not linked to a cutting sheet.')
                selected_rate_ids = {
                    int(value)
                    for value in request.form.getlist('special_operation_ids')
                    if str(value).isdigit()
                }
                valid_rate_ids = special_operation_ids.intersection(selected_rate_ids)
                valid_special_rates = OperationRate.query.filter(
                    OperationRate.id.in_(valid_rate_ids)
                ).all() if valid_rate_ids else []
                CutSpecialOperation.query.filter_by(
                    order_id=order.id,
                    cut_no=str(selected_cut),
                ).delete()
                for rate in valid_special_rates:
                    db.session.add(CutSpecialOperation(
                        order_id=order.id,
                        cut_no=str(selected_cut),
                        rate_id=rate.id,
                    ))
                db.session.commit()
                flash('Special operations saved for this cut.', 'success')
            except Exception as exc:
                db.session.rollback()
                flash(f'Could not save cut operations: {exc}', 'danger')
            redirect_args = {'job_no': job_no}
            if selected_cut:
                redirect_args['cut_no'] = selected_cut
            selected_operation = request.form.get('operation')
            if selected_operation:
                redirect_args['operation'] = selected_operation
            return redirect(url_for('production_entry', **redirect_args))

        job_data = request.form.get('job_no')
        job_no = None
        try:
            # Note: Agar prefill_job hai, toh job_no wahi use hoga
            # Agar nahi, toh form se aayega
            if job_data and '|' in job_data:
                parts = job_data.split('|')
                job_no = parts[0]
                party = parts[1]
            else:
                job_no = job_data
                order = Order.query.filter_by(job_no=job_no).first()
                party = order.name if order else "N/A"

            selected_cut = request.form.get('cut_no')
            selected_op = (request.form.get('operation') or '').strip().upper()
            pcs_value = int(request.form.get('pcs', 0) or 0)
            bq_unstitch_value = int(parse_numeric(request.form.get('bq_unstitch', 0)))
            bq_stitched_value = int(parse_numeric(request.form.get('bq_stitched', 0)))

            if pcs_value < 0 or bq_unstitch_value < 0 or bq_stitched_value < 0:
                raise ValueError('Production PCS and B/Q must not be negative.')

            if not selected_cut:
                raise ValueError("Select a cut number before saving.")

            cut_sheet = CuttingSheet.query.filter_by(order_id=job_no, cut_no=selected_cut).first()
            if not cut_sheet:
                raise ValueError("Selected cut number is not linked to a cutting sheet.")

            cut_limit = parse_numeric(cut_sheet.quantity)
            if cut_limit <= 0:
                raise ValueError("Invalid cut PCS configured for the selected cutting sheet.")

            selected_rates = get_rates_for_cut(order, selected_cut)
            operation_names = list(selected_rates.keys())
            if selected_op not in operation_names:
                raise ValueError("Selected operation is not configured for this order.")

            current_operation_index = operation_names.index(selected_op)
            production_logs = ProductionLog.query.filter_by(
                job_no=job_no,
                cut_no=selected_cut,
            ).all()
            production_state = get_cut_production_state(
                job_no,
                selected_cut,
                cut_limit,
                operation_names,
                logs=production_logs,
            )
            last_machine_index = max(
                (index for index, name in enumerate(operation_names)
                 if production_state['machine_operations'].get(name)),
                default=-1,
            )
            is_unstitched_operation = bool(
                production_state['machine_operations'].get(selected_op)
            )
            is_stitched_operation = bool(
                OperationRate.query.filter(
                    func.upper(OperationRate.operation) == selected_op
                ).with_entities(OperationRate.is_stitched_operation).scalar()
            )
            if bq_unstitch_value and is_stitched_operation:
                raise ValueError(
                    'B/Q Un-stitch cannot be entered for a Stitched Operation.'
                )
            is_stitched_stage = current_operation_index > last_machine_index
            if bq_stitched_value and not is_stitched_stage:
                raise ValueError(
                    'B/Q Stitched can only be entered after the machine operations are complete.'
                )
            bq_value = bq_stitched_value if is_stitched_stage else bq_unstitch_value
            if is_stitched_stage:
                previous_operation = operation_names[current_operation_index - 1] if current_operation_index > 0 else selected_op
                previous_inline_capacity = (
                    production_state['raw_totals'].get(previous_operation, 0)
                    + production_state['stitched_bq_totals'].get(previous_operation, 0)
                )
                if pcs_value + bq_stitched_value > previous_inline_capacity:
                    raise ValueError(
                        f"Cannot save entry. {selected_op} total of PCS + B/Q Stitched ({pcs_value + bq_stitched_value}) "
                        f"would exceed the inline PCS issued by {previous_operation} ({int(previous_inline_capacity)})."
                    )
            else:
                effective_bq_limit = bq_value
                input_limit = max(
                    0,
                    production_state['limits_before_bq'].get(selected_op, cut_limit) - effective_bq_limit,
                )
                if current_operation_index > 0:
                    previous_operation = operation_names[current_operation_index - 1]
                    previous_issued = production_state['raw_totals'].get(previous_operation, 0)
                    requested_from_previous = pcs_value + bq_value
                    existing_operation_total = production_state['raw_totals'].get(selected_op, 0)
                    if existing_operation_total <= 0 and requested_from_previous > previous_issued:
                        raise ValueError(
                            f"{selected_op} requires {requested_from_previous} PCS including B/Q, "
                            f"but {previous_operation} has issued only {int(previous_issued)} PCS."
                        )

                existing_total = db.session.query(func.coalesce(func.sum(ProductionLog.pcs), 0)).filter_by(
                    job_no=job_no,
                    cut_no=selected_cut,
                    operation=selected_op
                ).scalar() or 0

                existing_bq_total = production_state['bq_totals'].get(selected_op, 0)
                operation_limit = max(
                    0,
                    production_state['limits_before_bq'].get(selected_op, cut_limit)
                    - existing_bq_total,
                )
                updated_inline_limit = max(
                    0,
                    production_state['effective_limits'].get(selected_op, operation_limit)
                    - effective_bq_limit,
                )
                total_pcs_after_entry = existing_total + pcs_value
                total_bq_after_entry = existing_bq_total + bq_value
                original_consumption_after_entry = total_pcs_after_entry + total_bq_after_entry
                if total_pcs_after_entry > updated_inline_limit:
                    raise ValueError(
                        f"Cannot save entry. {selected_op} PCS would exceed the IN-LINE PCS limit of "
                        f"{int(updated_inline_limit)} for Cut No {selected_cut}. "
                        f"Current PCS: {int(existing_total)}, attempted PCS: {pcs_value}."
                    )
                if original_consumption_after_entry > cut_limit:
                    raise ValueError(
                        f"Cannot save entry. {selected_op} PCS plus B/Q would consume "
                        f"{int(original_consumption_after_entry)} of the original {int(cut_limit)} PCS "
                        f"limit for Cut No {selected_cut}."
                    )
            if is_stitched_stage:
                current_total = db.session.query(func.coalesce(func.sum(ProductionLog.pcs), 0)).filter_by(
                    job_no=job_no,
                    cut_no=selected_cut,
                    operation=selected_op
                ).scalar() or 0
                existing_stitched_bq = production_state['stitched_bq_totals'].get(selected_op, 0)
                if current_total + existing_stitched_bq + pcs_value + bq_stitched_value > previous_inline_capacity:
                    raise ValueError(
                        f"Cannot save entry. {selected_op} PCS plus B/Q Stitched must not exceed the inline PCS issued by {previous_operation} ({int(previous_inline_capacity)})."
                    )

            if (
                bq_unstitch_value
                and is_unstitched_operation
                and current_operation_index > 0
            ):
                deduct_previous_machine_operation_pieces(
                    job_no,
                    selected_cut,
                    operation_names,
                    current_operation_index,
                    production_state['machine_operations'],
                    bq_unstitch_value,
                )

            new_log = ProductionLog(
                date=request.form.get('date'),             
                job_no=job_no,
                party=party,
                article=request.form.get('article', ''),
                article_name=request.form.get('article_name', ''),
                order_style=request.form.get('order_style', ''),
                color=request.form.get('color', ''),
                file_no=request.form.get('file_no'), 
                cut_no=selected_cut, 
                cut_size=request.form.get('cut_size', ''),
                cut_pcs=int(cut_limit) if cut_limit is not None else None,
                bq_unstitch=bq_unstitch_value,
                bq_stitched=bq_stitched_value,
                worker=request.form.get('worker', ''),
                operation=selected_op,
                pcs=pcs_value
            )
            db.session.add(new_log)
            db.session.commit()
            flash(f"Production Entry saved for {job_no}!", "success")

            production_logs = ProductionLog.query.filter_by(
                job_no=job_no,
                cut_no=selected_cut,
            ).all()
            production_state = get_cut_production_state(
                job_no,
                selected_cut,
                cut_limit,
                operation_names,
                logs=production_logs,
            )
            operation_total = production_state['credited_totals'].get(selected_op, 0)
            operation_raw_total = production_state['raw_totals'].get(selected_op, 0)
            operation_limit = production_state['effective_limits'].get(
                selected_op,
                production_state['limits_before_bq'].get(selected_op, cut_limit),
            ) if production_state['machine_operations'].get(selected_op) else production_state['limits_before_bq'].get(selected_op, cut_limit)
            stitched_operation_names = {
                (rate.operation or '').upper()
                for rate in OperationRate.query.filter(
                    func.upper(OperationRate.operation).in_(operation_names)
                ).all()
                if rate.is_stitched_operation
            }
            operation_completion_total = operation_raw_total
            if selected_op in stitched_operation_names:
                operation_completion_total += production_state['stitched_bq_totals'].get(selected_op, 0)
                operation_limit = production_state['limits_before_bq'].get(selected_op, cut_limit)
            if operation_completion_total >= operation_limit:
                completed_operations = set()
                for operation_name in operation_names:
                    total = production_state['raw_totals'].get(operation_name, 0)
                    limit = production_state['effective_limits'].get(
                        operation_name,
                        production_state['limits_before_bq'].get(operation_name, cut_limit),
                    ) if production_state['machine_operations'].get(operation_name) else production_state['limits_before_bq'].get(operation_name, cut_limit)
                    if operation_name in stitched_operation_names:
                        total += production_state['stitched_bq_totals'].get(operation_name, 0)
                        limit = production_state['limits_before_bq'].get(operation_name, cut_limit)
                    if total >= limit:
                        completed_operations.add(operation_name)

                next_operation = next(
                    (
                        operation_name
                        for operation_name in operation_names[current_operation_index + 1:]
                        if operation_name not in completed_operations
                    ),
                    None
                )
                if next_operation is None:
                    next_operation = next(
                        (
                            operation_name
                            for operation_name in operation_names
                            if operation_name not in completed_operations
                        ),
                        None
                    )

                if next_operation is not None:
                    selected_operation = next_operation
                else:
                    current_cut_index = next(
                        (
                            index for index, sheet in enumerate(cutting_sheets)
                            if str(sheet.cut_no) == str(selected_cut)
                        ),
                        -1
                    )
                    next_sheet = (
                        cutting_sheets[current_cut_index + 1]
                        if current_cut_index >= 0 and current_cut_index + 1 < len(cutting_sheets)
                        else None
                    )
                    if next_sheet is not None:
                        selected_cut = str(next_sheet.cut_no)
                        selected_operation = (
                            resume_operations_by_cut.get(selected_cut)
                            or (operation_names[0] if operation_names else None)
                        )
            else:
                selected_operation = selected_op
            
        except Exception as e:
            db.session.rollback()
            flash(f"Error: {e}", "danger")

        redirect_args = {'job_no': job_no}
        if selected_cut:
            redirect_args['cut_no'] = selected_cut
        if selected_operation:
            redirect_args['operation'] = selected_operation
        return redirect(url_for('production_entry', **redirect_args))

    labour_workers = [w.name for w in Worker.query.filter_by(role='LABOUR').order_by(Worker.name).all()]
    return render_template(
        'production_entry.html', 
        parties=Order.query.all(), 
        workers=labour_workers, 
        rates=selected_rates,
        special_operations=special_operations,
        special_operation_names=special_operation_names,
        special_operation_ids_by_name=special_operation_ids_by_name,
        enabled_special_operation_ids_by_cut=enabled_special_operation_ids_by_cut,
        prefill_job=prefill_job,
        order=order,
        cutting_sheets=cutting_sheets,
        selected_cut=selected_cut,
        selected_operation=selected_operation,
        resume_operations_by_cut=resume_operations_by_cut,
        operation_limits_by_cut=operation_limits_by_cut,
        machine_operations_by_name=get_machine_operations(
            list(selected_rates.keys()) + [rate.operation for rate in special_operations]
        ),
        stitched_operations_by_name={
            (rate.operation or '').upper(): bool(rate.is_stitched_operation)
            for rate in OperationRate.query.filter(
                func.upper(OperationRate.operation).in_(selected_rates.keys())
            ).all()
        },
    )

@app.route('/manager/production-log', methods=['GET', 'POST'])
def production_log():
    if not session.get('role'): return redirect(url_for('index'))
    job_no = request.args.get('job_no') or request.args.get('filter_job')
    selected_cut = request.args.get('cut_no') or request.args.get('filter_cut')
    if request.method == 'POST':
        if session.get('role') not in ('owner', 'manager') or is_read_only_profile():
            flash('Only an owner or manager can delete production logs.', 'danger')
            return redirect(url_for('production_log', job_no=job_no, cut_no=selected_cut or None))
        selected_ids = set()
        for value in request.form.getlist('log_ids'):
            for item in str(value).split(','):
                if item.strip().isdigit():
                    selected_ids.add(int(item.strip()))
        logs_to_delete = ProductionLog.query.filter(ProductionLog.id.in_(selected_ids)).all() if selected_ids else []
        logs_to_delete = [
            log for log in logs_to_delete
            if str(log.job_no) == str(job_no)
            and (not selected_cut or str(log.cut_no) == str(selected_cut))
        ]
        if not logs_to_delete:
            flash('Select at least one production-log row to delete.', 'danger')
        else:
            for log in logs_to_delete:
                db.session.delete(log)
            db.session.commit()
            flash(f'{len(logs_to_delete)} production log record(s) deleted.', 'success')
        return redirect(url_for('production_log', job_no=job_no, cut_no=selected_cut or None))
    selected_order = Order.query.filter_by(job_no=job_no).first() if job_no else None
    if not selected_order:
        flash('Order not found. Please open a valid order first.', 'danger')
        return redirect(url_for('manager_dashboard'))

    logs = ProductionLog.query.order_by(ProductionLog.id.desc()).all()
    filtered_logs = []
    for log in logs:
        if job_no and str(log.job_no) != str(job_no):
            continue
        if selected_cut and str(log.cut_no) != str(selected_cut):
            continue
        filtered_logs.append(log)
    logs = filtered_logs
    operation_order_by_cut = {}
    job_numbers = {log.job_no for log in logs if log.job_no}
    if job_numbers:
        orders_by_job = {
            order.job_no: order
            for order in Order.query.filter(Order.job_no.in_(job_numbers)).all()
        }
        for current_job, order in orders_by_job.items():
            for sheet in CuttingSheet.query.filter_by(order_id=current_job).all():
                cut_operation_names = list(get_rates_for_cut(order, sheet.cut_no).keys())
                operation_order_by_cut[(current_job, str(sheet.cut_no))] = {
                    operation_name.upper(): position
                    for position, operation_name in enumerate(cut_operation_names)
                }

    logs.sort(key=lambda log: (
        operation_order_by_cut.get((log.job_no, str(log.cut_no)), {}).get((log.operation or '').upper(), 100000),
        (log.operation or '').upper(),
        log.date or '',
        log.id,
    ))
    cut_totals = {}
    cut_limits = {}
    cut_aq_limits = {}

    for log in logs:
        operation_key = (log.job_no, log.cut_no, log.operation)
        cut_totals[operation_key] = cut_totals.get(operation_key, 0) + (log.pcs or 0)

    all_cut_keys = {(log.job_no, log.cut_no) for log in logs if log.job_no and log.cut_no}
    for job_no, cut_no in all_cut_keys:
        cut_sheet = CuttingSheet.query.filter_by(order_id=job_no, cut_no=cut_no).first()
        if not cut_sheet:
            continue
        cut_pcs = parse_numeric(cut_sheet.quantity) or parse_numeric(cut_sheet.summary_total_pcs) or 0
        bq_unstitch_total = sum(
            parse_numeric(entry.bq_unstitch)
            for entry in ProductionLog.query.filter_by(job_no=job_no, cut_no=cut_no).all()
        )
        cut_aq_limits[(job_no, cut_no)] = max(0, int(round(cut_pcs - bq_unstitch_total)))

    for log in logs:
        operation_key = (log.job_no, log.cut_no, log.operation)
        cut_limit = cut_aq_limits.get((log.job_no, log.cut_no), 0)
        if cut_limit:
            cut_limits[operation_key] = cut_limit

    displayed_operation_keys = set(cut_totals)
    if displayed_operation_keys:
        displayed_job_numbers = {operation_key[0] for operation_key in displayed_operation_keys}
        all_cut_logs = ProductionLog.query.filter(
            ProductionLog.job_no.in_(displayed_job_numbers)
        ).all()
        cut_totals = {}
        for log in all_cut_logs:
            operation_key = (log.job_no, log.cut_no, log.operation)
            if operation_key not in displayed_operation_keys:
                continue
            cut_totals[operation_key] = cut_totals.get(operation_key, 0) + (log.pcs or 0)

    cut_complete_by_id = {
        log.id: cut_totals.get((log.job_no, log.cut_no, log.operation), 0) >= cut_limits.get((log.job_no, log.cut_no, log.operation), 0) > 0
        for log in logs
    }

    operation_state_by_cut = {}
    operation_type_by_name = {}
    if selected_order:
        all_order_logs = ProductionLog.query.filter_by(job_no=selected_order.job_no).all()
        for sheet in CuttingSheet.query.filter_by(order_id=selected_order.job_no).all():
            operation_names = list(get_rates_for_cut(selected_order, sheet.cut_no).keys())
            operation_type_by_name.update({
                (rate.operation or '').upper(): rate
                for rate in OperationRate.query.filter(
                    func.upper(OperationRate.operation).in_(operation_names)
                ).all()
            })
            operation_state_by_cut[str(sheet.cut_no)] = get_cut_production_state(
                selected_order.job_no,
                sheet.cut_no,
                parse_numeric(sheet.quantity),
                operation_names,
                logs=[log for log in all_order_logs if str(log.cut_no) == str(sheet.cut_no)],
            )

        stitched_completion_by_operation_cut = {}
        for operation_name, operation_rate in operation_type_by_name.items():
            if not operation_rate.is_stitched_operation:
                continue
            for cut_no in {log.cut_no for log in all_order_logs}:
                matching_logs = [
                    log for log in all_order_logs
                    if str(log.cut_no) == str(cut_no)
                    and (log.operation or '').upper() == operation_name
                ]
                if not matching_logs:
                    continue
                inline_qty = operation_state_by_cut.get(str(cut_no), {}).get(
                    'effective_limits', {}
                ).get(operation_name, 0)
                worked_pcs = sum(log.pcs or 0 for log in matching_logs)
                stitched_bq = sum(parse_numeric(log.bq_stitched) for log in matching_logs)
                stitched_completion_by_operation_cut[(operation_name, str(cut_no))] = (
                    inline_qty > 0 and worked_pcs + stitched_bq >= inline_qty
                )
        for log in logs:
            operation_name = (log.operation or '').upper()
            if (operation_name, str(log.cut_no)) in stitched_completion_by_operation_cut:
                cut_complete_by_id[log.id] = stitched_completion_by_operation_cut[
                    (operation_name, str(log.cut_no))
                ]

    displayed_logs = []
    for log in logs:
        operation_name = (log.operation or '').upper()
        operation_rate = operation_type_by_name.get(operation_name)
        is_unstitched = bool(operation_rate and operation_rate.is_machine_operation)
        bq_value = (
            parse_numeric(log.bq_unstitch)
            if is_unstitched
            else parse_numeric(log.bq_stitched)
        )
        if not is_unstitched and not bq_value and log.bq_unstitch:
            bq_value = parse_numeric(log.bq_unstitch)
        operation_state = operation_state_by_cut.get(str(log.cut_no), {})
        inline_pcs = operation_state.get('effective_limits', {}).get(operation_name, log.cut_pcs)
        pcs = log.pcs or 0
        qty = int(round(pcs))
        if operation_rate and operation_rate.is_stitched_operation:
            qty = int(round(qty + bq_value))
        displayed_logs.append(SimpleNamespace(
            id=log.id,
            operation=log.operation,
            date=log.date,
            party=log.party,
            article_name=log.article_name,
            color=log.color,
            job_no=log.job_no,
            file_no=log.file_no,
            cut_no=log.cut_no,
            cut_pcs=log.cut_pcs,
            worker=log.worker,
            pcs=pcs,
            bq=bq_value,
            qty=qty,
            bq_label='B/Q UNSTITCH' if is_unstitched else 'B/Q STITCH',
            inline_pcs=inline_pcs,
            log_ids=[log.id],
        ))
    logs = displayed_logs
    operation_rowspans = {}
    for index, log in enumerate(logs):
        operation_key = (log.operation or '').upper()
        if index == 0 or operation_key != (logs[index - 1].operation or '').upper():
            span = 1
            while index + span < len(logs) and (logs[index + span].operation or '').upper() == operation_key:
                span += 1
            operation_rowspans[index] = span

    selected_cutting_sheet = None
    if selected_order and selected_cut:
        selected_cutting_sheet = CuttingSheet.query.filter_by(
            order_id=selected_order.job_no,
            cut_no=selected_cut,
        ).order_by(CuttingSheet.id.desc()).first()

    selected_order_pcs = ''
    selected_order_month = ''
    if selected_order:
        selected_order_pcs = selected_order.new_qty_pcs or selected_order.qty or ''
        parsed_order_date = normalize_date(selected_order.date)
        selected_order_month = parsed_order_date.strftime('%b %Y') if parsed_order_date else (selected_order.date or '')

    return render_template(
        'production_log.html',
        logs=logs,
        current_job=job_no,
        selected_cut=selected_cut,
        cut_options=sorted({log.cut_no for log in ProductionLog.query.filter_by(job_no=job_no).all() if log.cut_no}, key=lambda value: (not str(value).isdigit(), int(value) if str(value).isdigit() else str(value))) if job_no else [],
        selected_order=selected_order,
        selected_order_month=selected_order_month,
        selected_order_pcs=selected_order_pcs,
        current_month_label=datetime.now().strftime('%b %Y'),
        selected_inventory_serial=selected_cutting_sheet.inventory_serial_no if selected_cutting_sheet else '',
        operation_rowspans=operation_rowspans,
        cut_complete_by_id=cut_complete_by_id
    )


@app.route('/manager/article/new', methods=['GET', 'POST'])
def new_article():
    if session.get('role') not in ('owner', 'manager'):
        return redirect(url_for('index'))

    edit_article_id = request.args.get('edit_article_id') or request.form.get('edit_article_id')
    edit_article = Article.query.get(edit_article_id) if edit_article_id else None
    if edit_article and is_read_only_profile():
        return reject_read_only_edit()

    item_master = ItemMaster.query.order_by(ItemMaster.item_name.asc()).all()
    item_master_data = [
        {
            'item_name': item.item_name,
            'material': item.material or '',
            'size': item.size or '',
            'unit': item.unit or '',
            'issue_unit': item.issue_unit or item.unit or '',
            'issue_unit_factor': float(item.issue_unit_factor or 1.0),
        }
        for item in item_master
    ]
    item_master_by_name = {
        item.item_name.strip().casefold(): item
        for item in item_master
        if item.item_name
    }

    if request.method == 'POST':
        article_no = normalize_article_no(request.form.get('article_no') or (edit_article.article_no if edit_article else generate_article_no()))
        duplicate_article = Article.query.filter_by(article_no=article_no).first()
        if duplicate_article and (not edit_article or duplicate_article.id != edit_article.id):
            flash(f'Article {article_no} already exists.', 'danger')
            return render_template('new_article.html', form=request.form, generated_article_no=article_no, item_master_data=item_master_data, edit_article=edit_article)

        article = edit_article or Article(article_no=article_no)
        article.article_no = article_no
        article.party_name = (request.form.get('party_name') or '').strip().upper()
        article.article_name = (request.form.get('article_name') or '').strip()
        article.style = (request.form.get('style') or '').strip()
        article.color = (request.form.get('color') or '').strip()
        article.finish_size = (request.form.get('finish_size') or '').strip()
        article.length = (request.form.get('length') or '').strip()
        article.width = (request.form.get('width') or '').strip()
        article.fabric_type = (request.form.get('fabric_type') or '').strip()
        article.pcs_per_side = (request.form.get('pcs_per_side') or '').strip()
        article.margin = (request.form.get('margin') or '').strip()
        if not article.party_name or not article.article_name or not article.style or not article.color:
            flash('Please complete party name, article name, style, and color.', 'danger')
            return render_template('new_article.html', form=request.form, generated_article_no=article_no, item_master_data=item_master_data, edit_article=edit_article)

        if not edit_article:
            db.session.add(article)
        db.session.flush()

        if edit_article:
            ArticleMaterialSpec.query.filter_by(article_id=article.id).delete()
        for idx in range(1, 11):
            item_name = (request.form.get(f'material_item_{idx}', '') or '').strip()
            material = (request.form.get(f'material_material_{idx}', '') or '').strip()
            size = (request.form.get(f'material_size_{idx}', '') or '').strip()
            qty = (request.form.get(f'material_qty_{idx}', '') or '').strip()
            unit = (request.form.get(f'material_unit_{idx}', '') or '').strip()
            item_type = (request.form.get(f'material_type_{idx}', '') or '').strip()
            master_item = item_master_by_name.get(item_name.casefold()) if item_name else None
            if not unit and master_item:
                unit = (master_item.unit or '').strip()
            if not item_name and not material and not size and not qty and not unit and not item_type:
                continue
            db.session.add(ArticleMaterialSpec(
                article_id=article.id,
                item_name=item_name or 'Item',
                material=material,
                size=size,
                qty_per_piece=qty,
                unit=unit,
                item_type=item_type,
                sort_order=idx,
            ))

        db.session.commit()
        if edit_article:
            linked_orders = Order.query.filter_by(article_id=article.id).all()
            for order in linked_orders:
                order.article_name = article.article_name
                order.style = article.style
                order.color = article.color
                order.name = article.party_name
            db.session.commit()
            flash(f'Article {article.article_no} updated successfully.', 'success')
        else:
            flash(f'Article {article.article_no} created successfully.', 'success')
        return redirect(url_for('article_operation_rates', article_id=article.id))

    form = {}
    if edit_article:
        form = {
            'article_no': edit_article.article_no or '',
            'party_name': edit_article.party_name or '',
            'article_name': edit_article.article_name or '',
            'style': edit_article.style or '',
            'color': edit_article.color or '',
            'finish_size': edit_article.finish_size or '',
            'length': edit_article.length or '',
            'width': edit_article.width or '',
            'fabric_type': edit_article.fabric_type or '',
            'pcs_per_side': edit_article.pcs_per_side or '',
            'margin': edit_article.margin or '',
        }
        for idx, spec in enumerate(edit_article.material_specs[:10], start=1):
            form[f'material_item_{idx}'] = spec.item_name or ''
            form[f'material_material_{idx}'] = spec.material or ''
            form[f'material_size_{idx}'] = spec.size or ''
            form[f'material_qty_{idx}'] = spec.qty_per_piece or ''
            master_item = item_master_by_name.get((spec.item_name or '').strip().casefold())
            form[f'material_unit_{idx}'] = spec.unit or (master_item.unit if master_item else '') or ''
            form[f'material_type_{idx}'] = spec.item_type or ''

    return render_template('new_article.html', form=form, generated_article_no=edit_article.article_no if edit_article else generate_article_no(), item_master_data=item_master_data, edit_article=edit_article)


@app.route('/manager/vendors', methods=['GET', 'POST'])
def vendors():
    if not session.get('role'):
        return redirect(url_for('index'))

    if request.method == 'POST':
        vendor_name = (request.form.get('vendor_name') or '').strip()
        if not vendor_name:
            flash('Vendor name is required.', 'danger')
            return redirect(url_for('vendors'))

        vendor = Vendor.query.filter(func.lower(func.trim(Vendor.name)) == vendor_name.lower()).first()
        if not vendor:
            vendor_code = (request.form.get('vendor_code') or '').strip() or None
            if vendor_code and Vendor.query.filter(func.lower(func.trim(Vendor.code)) == vendor_code.lower()).first():
                flash('A vendor with this code already exists.', 'danger')
                return redirect(url_for('vendors'))
            vendor = Vendor(
                name=vendor_name,
                code=vendor_code,
                contact_person=(request.form.get('contact_person') or '').strip(),
                phone=(request.form.get('phone') or '').strip(),
                email=(request.form.get('email') or '').strip(),
                address=(request.form.get('address') or '').strip(),
                notes=(request.form.get('notes') or '').strip(),
            )
            db.session.add(vendor)
            db.session.commit()
            flash('Vendor created successfully.', 'success')
        else:
            flash('Vendor already exists.', 'warning')
        return redirect(url_for('vendors'))

    vendors_list = Vendor.query.order_by(Vendor.name.asc()).all()
    vendor_items = VendorItem.query.all()
    return render_template(
        'vendors.html',
        vendors=vendors_list,
        total_vendor_items=len(vendor_items),
        priced_vendor_items=sum(1 for item in vendor_items if parse_numeric(item.rate) > 0),
        vendors_missing_contact=sum(1 for vendor in vendors_list if not (vendor.contact_person or vendor.phone or vendor.email)),
    )


@app.route('/manager/item-list', methods=['GET', 'POST'])
def item_list():
    if not session.get('role'):
        return redirect(url_for('index'))

    if request.method == 'POST':
        item_ids = request.form.getlist('item_id')
        item_names = request.form.getlist('item_name')
        materials = request.form.getlist('material')
        sizes = request.form.getlist('size')
        units = request.form.getlist('unit')
        issue_units = request.form.getlist('issue_unit')
        returnables = request.form.getlist('returnable')
        if is_read_only_profile():
            if any(item_id.strip() for item_id in item_ids) or any(
                ItemMaster.query.filter(func.lower(func.trim(ItemMaster.item_name)) == name.strip().lower()).first()
                for name in item_names if name and name.strip()
            ):
                return reject_read_only_edit('Saved items cannot be changed.')
        saved_count = 0

        for index, raw_name in enumerate(item_names):
            item_name = (raw_name or '').strip()
            if not item_name:
                continue

            item_id = int(item_ids[index]) if index < len(item_ids) and item_ids[index].isdigit() else None
            material = (materials[index] if index < len(materials) else '').strip()
            size = (sizes[index] if index < len(sizes) else '').strip()
            unit = (units[index] if index < len(units) else '').strip()
            issue_unit = (issue_units[index] if index < len(issue_units) else '').strip()
            if not issue_unit:
                issue_unit = unit
            is_returnable = index < len(returnables) and returnables[index] == '1'
            existing_item = ItemMaster.query.filter(
                func.lower(func.trim(ItemMaster.item_name)) == item_name.lower()
            ).first()

            if item_id:
                item = db.session.get(ItemMaster, item_id)
                if not item:
                    continue
                duplicate = ItemMaster.query.filter(
                    ItemMaster.id != item.id,
                    func.lower(func.trim(ItemMaster.item_name)) == item_name.lower()
                ).first()
                if duplicate:
                    continue
            elif existing_item:
                existing_item.material = material
                existing_item.size = size
                existing_item.unit = unit
                existing_item.issue_unit = issue_unit
                existing_item.issue_unit_factor = 1.0
                existing_item.returnable = is_returnable
                saved_count += 1
                continue
            else:
                item = ItemMaster(item_name=item_name)
                db.session.add(item)

            item.item_name = item_name
            item.material = material
            item.size = size
            item.unit = unit
            item.issue_unit = issue_unit
            item.issue_unit_factor = 1.0
            item.returnable = is_returnable
            saved_count += 1

        if not saved_count:
            flash('Add at least one item before saving.', 'danger')
            return redirect(url_for('item_list'))
        db.session.commit()
        flash(f'{saved_count} item(s) saved successfully.', 'success')
        return redirect(url_for('item_list'))

    items = ItemMaster.query.order_by(ItemMaster.item_name.asc()).all()
    return render_template('item_list.html', items=items, read_only_profile=is_read_only_profile())


@app.route('/manager/vendors/<int:vendor_id>', methods=['GET', 'POST'])
def vendor_detail(vendor_id):
    if not session.get('role'):
        return redirect(url_for('index'))

    vendor = Vendor.query.get_or_404(vendor_id)
    if request.method == 'POST':
        action = (request.form.get('action') or 'add_item').strip()
        if action == 'update_vendor':
            vendor_name = (request.form.get('vendor_name') or '').strip()
            vendor_code = (request.form.get('vendor_code') or '').strip() or None
            if not vendor_name:
                flash('Vendor name is required.', 'danger')
                return redirect(url_for('vendor_detail', vendor_id=vendor.id))
            duplicate_name = Vendor.query.filter(
                Vendor.id != vendor.id,
                func.lower(func.trim(Vendor.name)) == vendor_name.lower(),
            ).first()
            duplicate_code = Vendor.query.filter(
                Vendor.id != vendor.id,
                func.lower(func.trim(Vendor.code)) == vendor_code.lower(),
            ).first() if vendor_code else None
            if duplicate_name or duplicate_code:
                flash('Another vendor already uses that name or code.', 'danger')
                return redirect(url_for('vendor_detail', vendor_id=vendor.id))
            vendor.name = vendor_name
            vendor.code = vendor_code
            vendor.contact_person = (request.form.get('contact_person') or '').strip()
            vendor.phone = (request.form.get('phone') or '').strip()
            vendor.email = (request.form.get('email') or '').strip()
            vendor.address = (request.form.get('address') or '').strip()
            vendor.notes = (request.form.get('notes') or '').strip()
            db.session.commit()
            flash('Vendor profile updated.', 'success')
            return redirect(url_for('vendor_detail', vendor_id=vendor.id))

        if action == 'delete_item':
            item = VendorItem.query.filter_by(
                id=request.form.get('vendor_item_id', type=int),
                vendor_id=vendor.id,
            ).first()
            if item:
                db.session.delete(item)
                db.session.commit()
                flash('Vendor material removed.', 'success')
            else:
                flash('Vendor material was not found.', 'danger')
            return redirect(url_for('vendor_detail', vendor_id=vendor.id))

        item_name = (request.form.get('item_name') or '').strip()
        if not item_name:
            flash('Item name is required.', 'danger')
            return redirect(url_for('vendor_detail', vendor_id=vendor.id))

        pack_qty = parse_numeric(request.form.get('pack_qty', '0'))
        pack_price = parse_numeric(request.form.get('pack_price', request.form.get('rate', '0')))
        vendor_unit = (request.form.get('unit') or 'pcs').strip() or 'pcs'
        if is_roll_unit(vendor_unit) and pack_qty <= 0:
            flash('Enter the number of meters in one roll.', 'danger')
            return redirect(url_for('vendor_detail', vendor_id=vendor.id))
        unit_rate = pack_price if is_roll_unit(vendor_unit) else calculate_vendor_unit_rate(pack_qty, pack_price)
        if pack_qty <= 0 and pack_price <= 0:
            unit_rate = parse_numeric(request.form.get('rate', '0'))

        vendor_item_id = request.form.get('vendor_item_id', type=int)
        if action == 'update_item':
            vendor_item = VendorItem.query.filter_by(id=vendor_item_id, vendor_id=vendor.id).first()
            if not vendor_item:
                flash('Vendor material was not found.', 'danger')
                return redirect(url_for('vendor_detail', vendor_id=vendor.id))
        else:
            vendor_item = VendorItem(vendor_id=vendor.id)
            db.session.add(vendor_item)
        vendor_item.item_name = item_name
        vendor_item.material = (request.form.get('material') or '').strip()
        vendor_item.size = (request.form.get('size') or '').strip()
        vendor_item.unit = vendor_unit
        vendor_item.pack_qty = pack_qty
        vendor_item.pack_price = pack_price
        vendor_item.rate = unit_rate
        vendor_item.notes = (request.form.get('notes') or '').strip()
        db.session.commit()
        flash(f'Vendor material {"updated" if action == "update_item" else "added"}.', 'success')
        return redirect(url_for('vendor_detail', vendor_id=vendor.id))

    items = VendorItem.query.filter_by(vendor_id=vendor.id).order_by(VendorItem.id.asc()).all()
    item_master = ItemMaster.query.order_by(ItemMaster.item_name.asc()).all()
    selected_item = VendorItem.query.filter_by(
        id=request.args.get('edit_item', type=int),
        vendor_id=vendor.id,
    ).first() if request.args.get('edit_item', type=int) else None
    item_master_data = [
        {
            'item_name': item.item_name,
            'material': item.material or '',
            'size': item.size or '',
            'unit': item.unit or '',
            'issue_unit': item.issue_unit or item.unit or '',
            'issue_unit_factor': float(item.issue_unit_factor or 1.0),
        }
        for item in item_master
    ]
    return render_template(
        'vendor_detail.html',
        vendor=vendor,
        items=items,
        item_master=item_master,
        item_master_data=item_master_data,
        selected_item=selected_item,
        material_count=len(items),
        priced_material_count=sum(1 for item in items if parse_numeric(item.rate) > 0),
    )


@app.route('/manager/api/item-list')
def item_list_api():
    if not session.get('role'):
        return jsonify({'error': 'Unauthorized'}), 401

    items = ItemMaster.query.order_by(ItemMaster.item_name.asc()).all()
    return jsonify([
        {
            'item_name': item.item_name,
            'material': item.material or '',
            'size': item.size or '',
            'unit': item.unit or '',
            'issue_unit': item.issue_unit or item.unit or '',
            'issue_unit_factor': float(item.issue_unit_factor or 1.0),
        }
        for item in items
    ])


@app.route('/manager/api/vendor-items')
def vendor_items_api():
    if not session.get('role'):
        return jsonify({'error': 'Unauthorized'}), 401

    vendor_name = (request.args.get('vendor_name') or '').strip()
    if not vendor_name:
        return jsonify([])

    vendor = Vendor.query.filter(func.lower(Vendor.name) == vendor_name.lower()).first()
    if not vendor:
        return jsonify([])

    items = VendorItem.query.filter_by(vendor_id=vendor.id).order_by(VendorItem.id.asc()).all()
    return jsonify([
        {
            'item_name': item.item_name,
            'material': item.material,
            'size': item.size,
            'unit': item.unit,
            'pack_qty': float(item.pack_qty or 0),
            'roll_length_m': float(item.pack_qty or 0) if is_roll_unit(item.unit) else 0.0,
            'pack_price': float(item.pack_price or 0),
            'rate': float(item.rate or 0),
            'unit_rate': float(item.rate or 0),
            'notes': item.notes,
        }
        for item in items
    ])


@app.route('/manager/operation-rates', methods=['GET', 'POST'])
def operation_rates():
    if not session.get('role'):
        return redirect(url_for('index'))
    articles = Article.query.order_by(Article.article_no).all()
    article_order_counts = {
        article.id: Order.query.filter(
            or_(
                Order.article_id == article.id,
                Order.article == article.article_no,
                Order.article == display_article_no(article.article_no),
            )
        ).count()
        for article in articles
    }
    return render_template(
        'operation_rates.html',
        articles=articles,
        article_order_counts=article_order_counts,
    )


@app.route('/manager/operation-rates/article/<int:article_id>/orders')
def operation_article_orders(article_id):
    if not session.get('role'):
        return redirect(url_for('index'))

    article = Article.query.get_or_404(article_id)
    orders = Order.query.filter(
        or_(
            Order.article_id == article.id,
            func.lower(Order.article) == article.article_no.lower(),
            func.lower(Order.article) == display_article_no(article.article_no).lower(),
        )
    ).order_by(Order.id.desc()).all()
    return render_template('operation_article_orders.html', article=article, orders=orders)


@app.route('/manager/general-operation-rates', methods=['GET', 'POST'])
def general_operation_rates():
    if not session.get('role'):
        return redirect(url_for('index'))

    if request.method == 'POST':
        if is_read_only_profile() and (
            request.form.get('delete_operation_id') or request.form.get('operation_id')
        ):
            return reject_read_only_edit('This profile cannot manage general operation rates.')
        try:
            delete_id = request.form.get('delete_operation_id')
            if delete_id:
                rate_obj = OperationRate.query.get_or_404(delete_id)
                ArticleOperationRate.query.filter_by(rate_id=rate_obj.id).delete()
                ArticleOperationRateHistory.query.filter_by(rate_id=rate_obj.id).delete()
                CutSpecialOperation.query.filter_by(rate_id=rate_obj.id).delete()
                OperationRateHistory.query.filter_by(operation=rate_obj.operation.upper()).delete()
                db.session.delete(rate_obj)
                db.session.commit()
                flash('Operation deleted.', 'success')
                return redirect(url_for('general_operation_rates'))

            operation_id = request.form.get('operation_id')
            new_operation_name = (request.form.get('operation_name') or '').strip().upper()
            if operation_id and new_operation_name:
                rate_obj = OperationRate.query.get_or_404(operation_id)
                rate_obj.is_machine_operation = request.form.get('is_unstitched_operation') == 'on'
                rate_obj.is_stitched_operation = request.form.get('is_stitched_operation') == 'on'
                if rate_obj.is_machine_operation and rate_obj.is_stitched_operation:
                    raise ValueError('Choose either Unstitched Operation or Stitched Operation, not both.')
                if new_operation_name != rate_obj.operation:
                    if OperationRate.query.filter_by(operation=new_operation_name).first():
                        raise ValueError('Operation already exists.')
                    old_operation_name = rate_obj.operation.upper()
                    rate_obj.operation = new_operation_name
                    OperationRateHistory.query.filter_by(operation=old_operation_name).update(
                        {OperationRateHistory.operation: new_operation_name}
                    )

            new_operation = (request.form.get('new_operation') or '').strip().upper()
            if new_operation:
                if OperationRate.query.filter_by(operation=new_operation).first():
                    raise ValueError('Operation already exists.')
                new_rate_obj = OperationRate(
                    operation=new_operation,
                    rate=0.0,
                    is_machine_operation=request.form.get('new_is_unstitched_operation') == 'on',
                    is_stitched_operation=request.form.get('new_is_stitched_operation') == 'on',
                    updated_at=datetime.utcnow(),
                )
                if new_rate_obj.is_machine_operation and new_rate_obj.is_stitched_operation:
                    raise ValueError('Choose either Unstitched Operation or Stitched Operation, not both.')
                db.session.add(new_rate_obj)

            db.session.commit()
            flash('Operations updated.', 'success')
        except Exception as exc:
            db.session.rollback()
            flash(f'Could not update general rates: {exc}', 'danger')
        return redirect(url_for('general_operation_rates'))

    rates = OperationRate.query.order_by(OperationRate.operation).all()
    return render_template('general_operation_rates.html', rates=rates)


@app.route('/manager/operation-rates/article/<int:article_id>', methods=['GET', 'POST'])
def article_operation_rates(article_id):
    if not session.get('role'):
        return redirect(url_for('index'))

    article = Article.query.get_or_404(article_id)
    existing_assignments = ArticleOperationRate.query.filter_by(article_id=article.id).order_by(
        ArticleOperationRate.sort_order.asc(), ArticleOperationRate.id.asc()
    ).all()
    existing_rate_ids = {item.rate_id for item in existing_assignments}
    all_rates = OperationRate.query.order_by(OperationRate.operation).all()
    rates = (
        [rate for item in existing_assignments for rate in all_rates if rate.id == item.rate_id]
        + [rate for rate in all_rates if rate.id not in existing_rate_ids]
    )
    if request.method == 'POST':
        if is_read_only_profile() and existing_assignments:
            return reject_read_only_edit('This profile cannot edit article operation rates.')
        try:
            submitted_rate_ids = request.form.getlist('operation_order')
            if not submitted_rate_ids:
                submitted_rate_ids = [str(rate.id) for rate in rates]
            sort_order = 0
            saved_rate_ids = set()
            existing_by_rate_id = {item.rate_id: item for item in existing_assignments}
            for rate_id in submitted_rate_ids:
                if not str(rate_id).isdigit():
                    continue
                rate = OperationRate.query.get(int(rate_id))
                if not rate or rate.id in saved_rate_ids:
                    continue
                is_enabled = request.form.get(f'operation_{rate.id}') == 'on'
                is_special = request.form.get(f'special_operation_{rate.id}') == 'on'
                if not is_enabled and not is_special:
                    continue
                override_raw = (request.form.get(f'override_{rate.id}') or '').strip()
                override = float(override_raw) if override_raw else None
                assignment = existing_by_rate_id.get(rate.id)
                is_new_assignment = assignment is None
                previous_override = assignment.override_rate if assignment else None
                if assignment is None:
                    assignment = ArticleOperationRate(
                        article_id=article.id,
                        rate_id=rate.id,
                    )
                    db.session.add(assignment)
                assignment.override_rate = override
                assignment.is_enabled = is_enabled
                assignment.is_special_operation = is_special
                assignment.sort_order = sort_order
                if is_new_assignment or previous_override != override:
                    db.session.add(ArticleOperationRateHistory(
                        article_id=article.id,
                        rate_id=rate.id,
                        override_rate=override,
                        effective_date=datetime.utcnow(),
                        portal_name=get_active_portal_name(),
                    ))
                saved_rate_ids.add(rate.id)
                sort_order += 1
            for assignment in existing_assignments:
                if assignment.rate_id not in saved_rate_ids:
                    db.session.delete(assignment)
            db.session.commit()
            flash('Article operation rates saved.', 'success')
            return redirect(url_for('article_operation_rates', article_id=article.id))
        except Exception as exc:
            db.session.rollback()
            flash(f'Could not save article rates: {exc}', 'danger')

    assignments = {
        item.rate_id: item
        for item in ArticleOperationRate.query.filter_by(article_id=article.id).all()
    }
    article_rate_history_map = {}
    latest_histories = ArticleOperationRateHistory.query.filter_by(article_id=article.id).order_by(
        ArticleOperationRateHistory.rate_id.asc(),
        ArticleOperationRateHistory.effective_date.desc(),
        ArticleOperationRateHistory.id.desc(),
    ).all()
    for history in latest_histories:
        article_rate_history_map.setdefault(history.rate_id, history)
    return render_template(
        'article_operation_rates.html',
        article=article,
        rates=rates,
        assignments=assignments,
        article_rate_history_map=article_rate_history_map,
        prepared_by=session.get('name') or session.get('user') or 'System',
        current_year=datetime.utcnow().year,
    )


@app.route('/manager/summary', methods=['GET', 'POST'])
def summary():
    if not session.get('role'):
        return redirect(url_for('index'))

    filter_job = request.args.get('filter_job') or request.form.get('filter_job', '')
    filter_cut = request.args.get('filter_cut') or request.form.get('filter_cut', '')
    filter_item = request.args.get('filter_item') or request.form.get('filter_item', '')
    filter_date = request.args.get('filter_date') or request.form.get('filter_date', '')
    # New filter controls
    filter_type = request.args.get('filter_type') or request.form.get('filter_type') or 'MONTHLY'
    selected_month = request.args.get('filter_month') or request.form.get('filter_month') or datetime.now().strftime('%Y-%m')
    filter_week = request.args.get('filter_week') or request.form.get('filter_week') or '1-7'
    filter_start = request.args.get('filter_start') or request.form.get('filter_start') or ''
    filter_end = request.args.get('filter_end') or request.form.get('filter_end') or ''
    filter_worker = request.args.get('filter_worker') or request.form.get('filter_worker') or ''

    parties = Order.query.order_by(Order.id.desc()).all()
    selected_party = Order.query.filter_by(job_no=filter_job).first() if filter_job else None
    order = selected_party

    current_month = datetime.now().strftime('%Y-%m')
    filter_month = current_month
    if filter_date:
        parsed_filter = normalize_date(filter_date)
        if parsed_filter:
            filter_month = parsed_filter.strftime('%Y-%m')

    all_logs = ProductionLog.query.order_by(ProductionLog.operation, ProductionLog.worker, ProductionLog.cut_no).all()

    def cut_sort_key(cut_no):
        try:
            return int(str(cut_no))
        except ValueError:
            return cut_no

    def build_job_summary(job_no, job_logs, completion_logs):
        order_for_job = Order.query.filter_by(job_no=job_no).first()
        rates_map = get_rates_for_order(order_for_job)
        stitched_operation_names = {
            (rate.operation or '').upper()
            for rate in OperationRate.query.filter(
                func.upper(OperationRate.operation).in_([str(name).upper() for name in rates_map.keys()])
            ).all()
            if rate.is_stitched_operation
        }
        worker_employment_types = {}

        def summary_worker_is_attendance_based(worker_name):
            worker_key = (worker_name or 'UNKNOWN').strip().casefold()
            if worker_key not in worker_employment_types:
                worker = Worker.query.filter(
                    func.lower(func.trim(Worker.name)) == worker_key
                ).first()
                employment_type = str(getattr(worker, 'employment_type', '') or '').strip().lower()
                employment_type = employment_type.replace('-', '_').replace(' ', '_')
                worker_employment_types[worker_key] = employment_type in ('per_day', 'salaried')
            return worker_employment_types[worker_key]

        def summary_rate(log):
            if summary_worker_is_attendance_based(log.worker):
                return 0.0
            operation = (log.operation or '').upper()
            if operation in rates_map:
                return rates_map[operation]
            return get_rate_for_log(log)

        def summary_log_total(log):
            operation = (log.operation or '').upper()
            base_pcs = log.pcs or 0
            if operation in stitched_operation_names:
                return int(round(base_pcs + parse_numeric(log.bq_stitched)))
            return int(round(base_pcs))

        cutting_sheets = CuttingSheet.query.filter_by(order_id=job_no).all()
        cut_by_no = {}
        for sheet in cutting_sheets:
            cut_by_no.setdefault(str(sheet.cut_no), sheet)

        cut_numbers = sorted(cut_by_no.keys(), key=cut_sort_key)
        cuts = []
        cut_groups = [[]]
        for cut_no in cut_numbers:
            sheet = cut_by_no.get(cut_no)
            summary_total_value = parse_numeric(sheet.summary_total_pcs) if sheet and sheet.summary_total_pcs else None
            fallback_quantity = parse_numeric(sheet.quantity) if sheet and sheet.quantity else None
            cut_pcs = summary_total_value if summary_total_value is not None else fallback_quantity if fallback_quantity is not None else 0
            cut_logs = [log for log in job_logs if str(log.cut_no) == str(cut_no)]
            has_production_bq = any(log.bq_unstitch is not None or log.bq_stitched is not None for log in cut_logs)
            bq_unstitch_value = (
                sum(parse_numeric(log.bq_unstitch) for log in cut_logs)
                if has_production_bq
                else parse_numeric(sheet.bq_unstitch) if sheet and sheet.bq_unstitch else 0
            )
            bq_stitched_value = sum(parse_numeric(log.bq_stitched) for log in cut_logs)
            raw_shortage = parse_numeric(sheet.shortage) if sheet and sheet.shortage else 0
            shortage_value = abs(raw_shortage)
            total_aq = int(round(cut_pcs - bq_unstitch_value)) if sheet else ''
            cuts.append({
                'cut_no': cut_no,
                'label': f'CUT {cut_no}',
                'pcs': int(cut_pcs) if sheet and (sheet.summary_total_pcs or sheet.quantity) else 0,
                'cut_date': sheet.cut_date if sheet else '',
                'issue_date': sheet.issue_date if sheet else '',
                'bq_unstitch': int(bq_unstitch_value),
                'bq_stitched': int(bq_stitched_value),
                'shortage': int(shortage_value) if sheet and sheet.shortage else 0,
                'total_aq': total_aq
            })
        cut_groups = [cuts[index:index + 10] for index in range(0, len(cuts), 10)] or [[]]

        section_order = list(rates_map.keys())
        operation_names = sorted({log.operation for log in job_logs if log.operation}, key=lambda x: (section_order.index(x) if x in section_order else 999, x))

        summary_sections = []
        for op in operation_names:
            rows = []
            worker_map = {}
            for log in job_logs:
                if log.operation != op:
                    continue
                worker_name = log.worker or 'UNKNOWN'
                worker_map.setdefault(worker_name, {})
                worker_map[worker_name][str(log.cut_no)] = worker_map[worker_name].get(str(log.cut_no), 0) + summary_log_total(log)

            if not worker_map:
                continue

            section_total_pcs = 0
            section_total_amount = 0
            for worker_name, cuts_map in sorted(worker_map.items()):
                row_total = sum(cuts_map.values())
                row_amount = 0.0
                for l in job_logs:
                    if l.operation != op:
                        continue
                    if (l.worker or 'UNKNOWN') != worker_name:
                        continue
                    row_amount += summary_log_total(l) * summary_rate(l)

                row_rate = (row_amount / row_total) if row_total else 0.0
                rows.append({
                    'worker': worker_name,
                    'cuts': cuts_map,
                    'total': row_total,
                    'rate': row_rate,
                    'amount': row_amount
                })
                section_total_pcs += row_total
                section_total_amount += row_amount
            for row in rows:
                row['group_totals'] = [
                    sum(row['cuts'].get(cut['cut_no'], 0) for cut in cut_group)
                    for cut_group in cut_groups
                ]
                row['group_amounts'] = [
                    sum(
                        summary_log_total(log) * summary_rate(log)
                        for log in job_logs
                        if log.operation == op
                        and (log.worker or 'UNKNOWN') == row['worker']
                        and any(str(log.cut_no) == str(cut['cut_no']) for cut in cut_group)
                    )
                    for cut_group in cut_groups
                ]
            cut_totals = []
            for cut_no in cut_numbers:
                cut_totals.append(sum(row['cuts'].get(cut_no, 0) for row in rows))

            historical_cut_totals = []
            for cut_no in cut_numbers:
                historical_cut_totals.append(sum(
                    summary_log_total(log)
                    for log in completion_logs
                    if log.operation == op and str(log.cut_no) == str(cut_no)
                ))

            group_totals = [
                sum(cut_totals[index:index + len(cut_group)])
                for index, cut_group in ((start, group) for start, group in zip(
                    range(0, len(cut_totals), 10), cut_groups
                ))
            ] or [0]
            group_amounts = [sum(row['group_amounts'][index] for row in rows) for index in range(len(cut_groups))]
            group_rates = [
                (group_amounts[index] / group_totals[index]) if group_totals[index] else 0.0
                for index in range(len(cut_groups))
            ]

            section_rate = (section_total_amount / section_total_pcs) if section_total_pcs else 0.0
            summary_sections.append({
                'operation': op,
                'rows': rows,
                'cut_totals': cut_totals,
                'historical_cut_totals': historical_cut_totals,
                'group_totals': group_totals,
                'group_rates': group_rates,
                'group_amounts': group_amounts,
                'total': section_total_pcs,
                'rate': section_rate,
                'amount': section_total_amount
            })

        # Build a human friendly period label based on current filter selection
        period_label = ''
        try:
            if filter_type == 'MONTHLY':
                # Show full month name and year in uppercase, e.g. 'AUGUST 2026'
                period_label = datetime.strptime(selected_month, '%Y-%m').strftime('%B %Y').upper()
            elif filter_type == 'WEEKLY':
                # parse selected_month like YYYY-MM and week like '1-7'
                y, m = map(int, selected_month.split('-'))
                start_day, end_day = map(int, (filter_week or '1-7').split('-'))
                last_day = calendar.monthrange(y, m)[1]
                end_day = min(end_day, last_day)
                start_dt = datetime(y, m, start_day)
                end_dt = datetime(y, m, end_day)
                period_label = f"{start_dt.strftime('%d-%b-%Y')} to {end_dt.strftime('%d-%b-%Y')}"
            elif filter_type == 'CUSTOM':
                s = normalize_date(filter_start) if filter_start else None
                e = normalize_date(filter_end) if filter_end else None
                if s and e:
                    period_label = f"{s.strftime('%d-%b-%Y')} to {e.strftime('%d-%b-%Y')}"
                elif s:
                    period_label = f"From {s.strftime('%d-%b-%Y')}"
                elif e:
                    period_label = f"Up to {e.strftime('%d-%b-%Y')}"
                else:
                    period_label = selected_month
            else:
                period_label = selected_month
        except Exception:
            period_label = selected_month

        return {
            'job_no': job_no,
            'order': order_for_job,
            'cuts': cuts,
            'cut_groups': cut_groups,
            'summary_sections': summary_sections,
            'display_item': filter_item or (order_for_job.article_name or order_for_job.article if order_for_job else 'DIPER (2X3X2)'),
            'display_party': order_for_job.name if order_for_job else job_no,
            'display_file_no': order_for_job.file_no if order_for_job else '',
            'display_date': (order_for_job.date if order_for_job and order_for_job.date else filter_date) or '',
            'display_period': period_label,
            'display_month': selected_month
        }

    # compute available workers for filter dropdown
    workers = sorted({(l.worker or '').strip() for l in all_logs if l.worker})

    # start with all logs and apply filters
    logs = list(all_logs)
    if filter_job:
        logs = [log for log in logs if str(log.job_no) == str(filter_job)]

    if filter_worker:
        logs = [log for log in logs if (log.worker or '').strip() == filter_worker]

    # Date-based filtering
    if filter_type == 'MONTHLY':
        month = selected_month
        logs = [log for log in logs if normalize_date(log.date) and normalize_date(log.date).strftime('%Y-%m') == month]
    elif filter_type == 'WEEKLY':
        month = selected_month
        week_map = {'1-7': (1, 7), '8-14': (8, 14), '15-21': (15, 21), '22-30': (22, 31)}
        start_day, end_day = week_map.get(filter_week, (1, 31))
        filtered = []
        for log in logs:
            nd = normalize_date(log.date)
            if not nd:
                continue
            if nd.strftime('%Y-%m') != month:
                continue
            if nd.day >= start_day and nd.day <= end_day:
                filtered.append(log)
        logs = filtered
    elif filter_type == 'CUSTOM':
        start_dt = normalize_date(filter_start) if filter_start else None
        end_dt = normalize_date(filter_end) if filter_end else None
        if start_dt or end_dt:
            filtered = []
            for log in logs:
                nd = normalize_date(log.date)
                if not nd:
                    continue
                if start_dt and nd < start_dt:
                    continue
                if end_dt and nd > end_dt:
                    continue
                filtered.append(log)
            logs = filtered

    # Keep the visible summary limited to the selected period, but include all
    # production up to that period when determining whether an operation is complete.
    completion_logs = list(all_logs)
    completion_end = None
    if filter_type == 'MONTHLY':
        year, month = map(int, selected_month.split('-'))
        completion_end = datetime(year, month, calendar.monthrange(year, month)[1])
    elif filter_type == 'WEEKLY':
        year, month = map(int, selected_month.split('-'))
        _, end_day = {'1-7': (1, 7), '8-14': (8, 14), '15-21': (15, 21), '22-30': (22, 31)}.get(filter_week, (1, 31))
        completion_end = datetime(year, month, min(end_day, calendar.monthrange(year, month)[1]))
    elif filter_type == 'CUSTOM':
        completion_end = normalize_date(filter_end) if filter_end else None

    if completion_end:
        completion_logs = [
            log for log in completion_logs
            if normalize_date(log.date) and normalize_date(log.date) <= completion_end
        ]

    job_numbers = sorted({str(log.job_no) for log in logs if log.job_no})
    job_summaries = [
        build_job_summary(
            job_no,
            [log for log in logs if str(log.job_no) == str(job_no)],
            [log for log in completion_logs if str(log.job_no) == str(job_no)]
        )
        for job_no in job_numbers
    ]

    return render_template(
        'summary.html',
        logs=logs,
        parties=parties,
        selected_party=selected_party,
        order=order,
        filter_job=filter_job,
        filter_cut=filter_cut,
        filter_item=filter_item,
        filter_date=filter_date,
        filter_type=filter_type,
        current_filter=filter_type,
        current_month=selected_month,
        current_week=filter_week,
        custom_start=filter_start,
        custom_end=filter_end,
        filter_worker=filter_worker,
        workers=workers,
        rates=get_rates_dict(),
        job_summaries=job_summaries,
        current_month_display=selected_month,
        current_calendar_month=datetime.now().strftime('%B %Y').upper()
    )

@app.route('/manager/job-sheet', methods=['GET', 'POST'])
def job_sheet():
    if not session.get('role'):
        return redirect(url_for('index'))

    try:
        db_workers = [w.name for w in Worker.query.filter(Worker.name.isnot(None)).order_by(Worker.name).all()]
    except Exception:
        db_workers = []
    default_worker = session.get('worker_name') or (db_workers[0] if db_workers else '')
    filter_worker = request.args.get('filter_worker') or request.form.get('filter_worker') or default_worker
    filter_job = request.args.get('filter_job') or request.args.get('job_no') or ''

    # Filtering options: MONTHLY, HALF, WEEKLY, CUSTOM
    filter_type = request.args.get('filter_type') or request.form.get('filter_type') or 'MONTHLY'
    selected_month = request.args.get('filter_month') or request.form.get('filter_month') or datetime.now().strftime('%Y-%m')
    week_choice = request.args.get('filter_week') or request.form.get('filter_week') or '1-7'
    half_choice = request.args.get('filter_half') or request.form.get('filter_half') or '1-15'
    custom_start = request.args.get('filter_start') or request.form.get('filter_start') or ''
    custom_end = request.args.get('filter_end') or request.form.get('filter_end') or ''
    selected_department = (request.args.get('department_filter') or request.form.get('department_filter') or '').strip()

    if request.method == 'POST' and request.form.get('form_action') == 'add_job_sheet_row':
        row_date = (request.form.get('additional_date') or '').strip()
        row_worker = (request.form.get('additional_worker') or '').strip()
        if row_date and row_worker:
            try:
                pcs = int(float(request.form.get('additional_pcs') or 0))
            except (TypeError, ValueError):
                pcs = 0
            try:
                rate = float(request.form.get('additional_rate') or 0)
            except (TypeError, ValueError):
                rate = 0.0
            db.session.add(JobSheetAdditional(
                date=row_date,
                worker=row_worker,
                party=(request.form.get('additional_party') or '').strip(),
                article_name=(request.form.get('additional_article') or '').strip(),
                order_style=(request.form.get('additional_style') or '').strip(),
                color=(request.form.get('additional_color') or '').strip(),
                file_no=(request.form.get('additional_file_no') or '').strip(),
                cut_no=(request.form.get('additional_cut') or '').strip(),
                operation=(request.form.get('additional_operation') or '').strip(),
                pcs=pcs,
                rate=rate,
            ))
            db.session.commit()
        return redirect(url_for(
            'job_sheet',
            department_filter=selected_department,
            filter_job=filter_job,
            filter_type=filter_type,
            filter_month=selected_month,
            filter_week=week_choice,
            filter_half=half_choice,
            filter_start=custom_start,
            filter_end=custom_end,
        ))

    if request.method == 'POST' and request.form.get('form_action') == 'delete_job_sheet_row':
        if is_read_only_profile():
            return reject_read_only_edit('Saved job-sheet rows cannot be deleted.')
        row_id = request.form.get('additional_row_id', type=int)
        row = JobSheetAdditional.query.get(row_id) if row_id else None
        if row:
            db.session.delete(row)
            db.session.commit()
        return redirect(url_for(
            'job_sheet',
            department_filter=selected_department,
            filter_job=filter_job,
            filter_type=filter_type,
            filter_month=selected_month,
            filter_week=week_choice,
            filter_half=half_choice,
            filter_start=custom_start,
            filter_end=custom_end,
        ))

    department_list = Department.query.order_by(func.lower(Department.name)).all()
    department_names = [dept.name.strip() for dept in department_list if dept.name and dept.name.strip()]
    if selected_department:
        selected_department_key = selected_department.casefold()
        selected_department = next(
            (name for name in department_names if name.casefold() == selected_department_key),
            ''
        )

    worker_departments = {
        worker.name.strip().lower(): (worker.department or '').strip()
        for worker in Worker.query.filter(Worker.name.isnot(None)).all()
    }
    department_supervisors = {}
    for worker in Worker.query.filter(Worker.name.isnot(None)).order_by(Worker.name).all():
        department = (worker.department or '').strip().casefold()
        sub_designation = (worker.sub_designation or '').strip().casefold()
        if department and sub_designation == 'supervisor' and department not in department_supervisors:
            department_supervisors[department] = worker.name.strip()

    logs = ProductionLog.query.order_by(ProductionLog.id.desc()).all()

    filtered_logs = []
    for log in logs:
        if filter_job and str(log.job_no) != str(filter_job):
            continue
        if not log.date:
            continue

        log_date = str(log.date)  # expected YYYY-MM-DD

        try:
            if filter_type == 'MONTHLY':
                if not log_date.startswith(selected_month):
                    continue
            elif filter_type.startswith('WEEKLY'):
                if not log_date.startswith(selected_month):
                    continue
                day = int(log_date[8:10])
                if week_choice == '1-7' and not (1 <= day <= 7):
                    continue
                if week_choice == '8-14' and not (8 <= day <= 14):
                    continue
                if week_choice == '15-21' and not (15 <= day <= 21):
                    continue
                if week_choice == '22-30' and not (22 <= day <= 31):
                    continue
            elif filter_type == 'HALF':
                if not log_date.startswith(selected_month):
                    continue
                day = int(log_date[8:10])
                if half_choice == '1-15' and not (1 <= day <= 15):
                    continue
                if half_choice == '16-end' and not (16 <= day <= 31):
                    continue
            elif filter_type == 'CUSTOM':
                if custom_start and custom_end:
                    if not (custom_start <= log_date <= custom_end):
                        continue
                else:
                    # if custom selected but dates missing, treat as no filter
                    pass
        except Exception:
            continue

        if selected_department:
            worker_department = worker_departments.get(str(log.worker or '').strip().lower(), '')
            if worker_department.casefold() != selected_department.casefold():
                continue

        filtered_logs.append(log)

    additional_rows = []
    for row in JobSheetAdditional.query.order_by(JobSheetAdditional.date.asc(), JobSheetAdditional.id.asc()).all():
        if not row.date:
            continue
        row_date = str(row.date)
        try:
            if filter_type == 'MONTHLY' and not row_date.startswith(selected_month):
                continue
            elif filter_type.startswith('WEEKLY'):
                if not row_date.startswith(selected_month):
                    continue
                day = int(row_date[8:10])
                week_bounds = {'1-7': (1, 7), '8-14': (8, 14), '15-21': (15, 21), '22-30': (22, 31)}
                start_day, end_day = week_bounds.get(week_choice, (1, 31))
                if not (start_day <= day <= end_day):
                    continue
            elif filter_type == 'HALF':
                if not row_date.startswith(selected_month):
                    continue
                day = int(row_date[8:10])
                if half_choice == '1-15' and not (1 <= day <= 15):
                    continue
                if half_choice == '16-end' and not (16 <= day <= 31):
                    continue
            elif filter_type == 'CUSTOM' and custom_start and custom_end:
                if not (custom_start <= row_date <= custom_end):
                    continue
        except Exception:
            continue

        if filter_job:
            continue
        if selected_department:
            worker_department = worker_departments.get(str(row.worker or '').strip().lower(), '')
            if worker_department.casefold() != selected_department.casefold():
                continue
        additional_rows.append(row)

    return render_template(
        'job_sheet.html',
        logs=filtered_logs,
        additional_rows=additional_rows,
        workers=db_workers,
        filter_worker=filter_worker,
        rates=get_rates_dict(),
        rate_for_log=get_rate_for_log,
        filter_job=filter_job,
        current_filter=filter_type,
        current_month=selected_month,
        current_week=week_choice,
        current_half=half_choice,
        custom_start=custom_start,
        custom_end=custom_end,
        departments=department_list,
        selected_department=selected_department,
        worker_departments=worker_departments,
        department_supervisors=department_supervisors,
    )

def calculate_payroll_payment_amount(worker, payout_portal, period_start, period_end, exclude_payment_id=None):
    if not period_start or not period_end:
        return 0.0
    if payout_portal == 'wages':
        logs = ProductionLog.query.filter(
            func.lower(func.trim(ProductionLog.worker)) == worker.name.strip().lower(),
            ProductionLog.date >= period_start,
            ProductionLog.date <= period_end,
        ).all()
        return round(sum((log.pcs or 0) * get_rate_for_log(log) for log in logs), 2)

    paid_ranges = [
        (payment.period_start, payment.period_end)
        for payment in SalaryPayment.query.filter_by(
            worker_id=worker.id,
            payout_portal=payout_portal,
        ).all()
        if payment.id != exclude_payment_id and payment.period_start and payment.period_end
    ]
    attendance_rows = DailyAttendance.query.filter(
        DailyAttendance.worker_id == worker.id,
        DailyAttendance.date >= period_start,
        DailyAttendance.date <= period_end,
    ).all()
    unpaid_rows = [
        row for row in attendance_rows
        if not any(start <= row.date <= end for start, end in paid_ranges)
    ]

    period_fully_paid = False
    if paid_ranges:
        uncovered_start = datetime.strptime(period_start, '%Y-%m-%d').date()
        required_end = datetime.strptime(period_end, '%Y-%m-%d').date()
        for paid_start, paid_end in sorted(paid_ranges):
            paid_start_date = datetime.strptime(paid_start, '%Y-%m-%d').date()
            paid_end_date = datetime.strptime(paid_end, '%Y-%m-%d').date()
            if paid_end_date < uncovered_start:
                continue
            if paid_start_date > uncovered_start:
                break
            if paid_end_date >= required_end:
                period_fully_paid = True
                break
            uncovered_start = paid_end_date + timedelta(days=1)
    attendance_rows = unpaid_rows if unpaid_rows or not period_fully_paid else attendance_rows
    if not attendance_rows:
        return 0.0

    present_days = sum(row.status == 'P' for row in attendance_rows)
    late_hours = sum(float(row.late_hours or 0.0) for row in attendance_rows)
    early_hours = sum(float(row.early_hours or 0.0) for row in attendance_rows)
    overtime_hours = payroll_overtime_hours(attendance_rows)
    night_hours = sum(float(row.night_hours or 0.0) for row in attendance_rows)

    if payout_portal == 'per_day':
        daily_rate = float(worker.salary or 0.0)
        hourly_rate = daily_rate / 8.0
        gross_amount = present_days * daily_rate
    else:
        try:
            year, month = (int(value) for value in period_start[:7].split('-', 1))
            days_in_month = calendar.monthrange(year, month)[1]
        except (TypeError, ValueError):
            return 0.0
        monthly_salary = float(worker.salary or 0.0) + float(worker.attendance_allowance or 0.0)
        hourly_rate = monthly_salary / days_in_month / 8.0
        gross_amount = present_days * monthly_salary / days_in_month

    calculated_amount = gross_amount + (
        -(late_hours + early_hours) * hourly_rate
        + (overtime_hours + night_hours) * hourly_rate
    )
    lower_amount = int(calculated_amount // 10) * 10
    rounded_amount = lower_amount if calculated_amount - lower_amount <= 5 else lower_amount + 10
    return round(rounded_amount, 2)


@app.route('/payout/mark-paid', methods=['POST'])
def mark_payout_paid():
    if not session.get('role'):
        return jsonify({'ok': False, 'error': 'Not logged in'}), 401

    selected_department = (request.form.get('department_filter') or '').strip()
    payout_company = (request.form.get('company') or '').strip().title()
    if payout_company not in ('Canon', 'Haram'):
        return jsonify({'ok': False, 'error': 'Choose whether Canon or Haram is paying this payroll.'}), 400
    filter_type = request.form.get('filter_type') or 'MONTHLY'
    selected_month = request.form.get('payout_month') or datetime.now().strftime('%Y-%m')
    selected_week = request.form.get('payout_week') or '1-7'
    selected_half = request.form.get('payout_half') or '1-15'
    custom_start = request.form.get('filter_start') or ''
    custom_end = request.form.get('filter_end') or ''
    payout_portal = (request.form.get('portal') or '').strip().lower()
    if payout_portal in ('labour', 'office_staff', 'staff'):
        payout_portal = {'labour': 'wages', 'office_staff': 'salaried', 'staff': 'salaried'}[payout_portal]
    if payout_portal not in ('wages', 'salaried', 'per_day'):
        payout_portal = ''

    selected_worker_ids = set()
    for worker_id in request.form.getlist('selected_worker_ids'):
        try:
            selected_worker_ids.add(int(worker_id))
        except (TypeError, ValueError):
            continue
    if not selected_worker_ids:
        return jsonify({'ok': False, 'error': 'Select at least one employee before marking payroll as paid.'}), 400

    period_start = None
    period_end = None
    month_label = ''
    if selected_month:
        try:
            month_label = datetime.strptime(selected_month, '%Y-%m').strftime('%b %Y').upper()
        except Exception:
            month_label = ''

    try:
        if filter_type in ('MONTHLY', 'WEEKLY', 'HALF'):
            year, month = (int(value) for value in selected_month.split('-', 1))
            month_last_day = calendar.monthrange(year, month)[1]
            start_day, end_day = (1, month_last_day)
            if filter_type == 'WEEKLY':
                start_day, end_day = (int(value) for value in selected_week.split('-', 1))
                end_day = min(end_day, month_last_day)
            elif filter_type == 'HALF':
                if selected_half == '1-15':
                    start_day, end_day = (1, 15)
                else:
                    start_day, end_day = (16, month_last_day)
            period_start = f'{year:04d}-{month:02d}-{start_day:02d}'
            period_end = f'{year:04d}-{month:02d}-{end_day:02d}'
        elif filter_type == 'CUSTOM':
            period_start = custom_start or None
            period_end = custom_end or None
    except Exception:
        period_start = None
        period_end = None

    if not period_start or not period_end:
        return jsonify({'ok': False, 'error': 'No valid period selected'}), 400

    workers_query = Worker.query
    if selected_department:
        workers_query = workers_query.filter(func.lower(func.trim(Worker.department)) == selected_department.lower())
    if payout_portal == 'per_day':
        workers_query = workers_query.filter(func.upper(func.trim(Worker.employment_type)) == 'PER DAY')
    elif payout_portal == 'salaried':
        workers_query = workers_query.filter(func.upper(func.trim(Worker.employment_type)) == 'SALARIED')
    elif payout_portal == 'wages':
        workers_query = workers_query.filter(func.upper(func.trim(Worker.employment_type)) == 'WAGES')

    workers = workers_query.order_by(Worker.name.asc()).all()
    workers = [worker for worker in workers if worker.id in selected_worker_ids]
    paid_count = 0

    for worker in workers:
        period_label = month_label
        if filter_type == 'WEEKLY':
            period_label = f'({selected_week}) {month_label}' if month_label else selected_week
        elif filter_type == 'HALF':
            period_label = f'(1-15) {month_label}' if selected_half == '1-15' else f'(16-MONTH END) {month_label}'
        elif filter_type == 'CUSTOM' and custom_start and custom_end:
            try:
                start_dt = datetime.strptime(custom_start, '%Y-%m-%d')
                end_dt = datetime.strptime(custom_end, '%Y-%m-%d')
                period_label = f'({start_dt.strftime("%d-%m-%Y")} - {end_dt.strftime("%d-%m-%Y")})'
            except Exception:
                period_label = f'({custom_start} - {custom_end})'

        existing_payment = SalaryPayment.query.filter_by(
            worker_id=worker.id,
            payout_portal=payout_portal,
            period_start=period_start,
            period_end=period_end
        ).first()
        if not existing_payment:
            db.session.add(SalaryPayment(
                worker_id=worker.id,
                department=selected_department or 'ALL DEPARTMENTS',
                payout_portal=payout_portal,
                company=payout_company,
                period_type=filter_type,
                period_label=period_label,
                period_start=period_start,
                period_end=period_end,
                amount=calculate_payroll_payment_amount(
                    worker, payout_portal, period_start, period_end
                ),
                paid_at=datetime.utcnow()
            ))
            paid_count += 1

        outstanding_advances = [
            a for a in WorkerAdvance.query.filter_by(worker_id=worker.id).filter(WorkerAdvance.record_type == 'advance').all()
            if a.date and a.amount and a.amount > 0
        ]
        outstanding_total = sum(float(entry.amount or 0.0) for entry in outstanding_advances)
        paid_against_advance = 0.0
        for entry in outstanding_advances:
            if entry.is_paid and entry.paid_period == period_label:
                continue
            if entry.date and period_start and period_end and period_start <= entry.date <= period_end:
                paid_against_advance += float(entry.amount or 0.0)
        if paid_against_advance > 0:
            existing_payment_record = WorkerAdvance.query.filter_by(
                worker_id=worker.id,
                record_type='payment',
                paid_period=period_label
            ).first()
            if not existing_payment_record:
                db.session.add(WorkerAdvance(
                    worker_id=worker.id,
                    amount=paid_against_advance,
                    date=period_end,
                    record_type='payment',
                    note=f'Auto payment for {period_label}',
                    is_paid=True,
                    paid_period=period_label,
                    paid_at=datetime.utcnow()
                ))
            for entry in outstanding_advances:
                if entry.date and period_start and period_end and period_start <= entry.date <= period_end:
                    entry.is_paid = True
                    entry.paid_period = period_label
                    entry.paid_at = datetime.utcnow()

    db.session.commit()
    return jsonify({'ok': True, 'count': paid_count})


@app.route('/manager/payout_sheet', methods=['GET', 'POST'])
def payout():
    if not session.get('role'):
        return redirect(url_for('index'))

    # New flexible filters: MONTHLY, WEEKLY (1-7,8-14,15-21,22-30), CUSTOM
    selected_job = request.form.get('job_no') or request.args.get('job_no') or request.args.get('filter_job') or ''
    filter_type = request.form.get('filter_type') or request.args.get('filter_type') or 'MONTHLY'
    selected_month = request.form.get('payout_month') or request.args.get('payout_month') or datetime.now().strftime('%Y-%m')
    selected_week = request.form.get('payout_week') or request.args.get('payout_week') or '1-7'
    selected_half = request.form.get('payout_half') or request.args.get('payout_half') or '1-15'
    custom_start = request.form.get('filter_start') or request.args.get('filter_start') or ''
    custom_end = request.form.get('filter_end') or request.args.get('filter_end') or ''
    selected_department = request.form.get('department_filter') or request.args.get('department_filter') or ''
    selected_department = (selected_department or '').strip()
    payout_portal = (request.form.get('portal') or request.args.get('portal') or '').strip().lower()
    if payout_portal in ('labour', 'office_staff', 'staff'):
        payout_portal = {'labour': 'wages', 'office_staff': 'salaried', 'staff': 'salaried'}[payout_portal]
    if payout_portal not in ('wages', 'salaried', 'per_day'):
        payout_portal = ''
    available_payout_portals = sorted({
        str(worker.employment_type).strip().lower().replace(' ', '_')
        for worker in Worker.query.all()
        if worker.employment_type and str(worker.employment_type).strip().lower().replace(' ', '_') in ('wages', 'salaried', 'per_day')
    })
    if payout_portal and payout_portal not in available_payout_portals:
        payout_portal = ''
    department_list = Department.query.order_by(func.lower(Department.name)).all()
    department_names = [dept.name.strip() for dept in department_list if dept.name and dept.name.strip()]
    if selected_department and selected_department not in department_names:
        selected_department = ''

    logs = ProductionLog.query.order_by(ProductionLog.id.desc()).all()
    filtered_logs = []

    for log in logs:
        if selected_job and str(log.job_no) != str(selected_job):
            continue
        if not log.date:
            continue

        log_date = str(log.date)

        try:
            if filter_type == 'MONTHLY':
                if not log_date.startswith(selected_month):
                    continue
            elif filter_type == 'WEEKLY':
                if not log_date.startswith(selected_month):
                    continue
                day = int(log_date[8:10])
                if selected_week == '1-7' and not (1 <= day <= 7):
                    continue
                if selected_week == '8-14' and not (8 <= day <= 14):
                    continue
                if selected_week == '15-21' and not (15 <= day <= 21):
                    continue
                if selected_week == '22-30' and not (22 <= day <= 31):
                    continue
            elif filter_type == 'HALF':
                if not log_date.startswith(selected_month):
                    continue
                day = int(log_date[8:10])
                if selected_half == '1-15' and not (1 <= day <= 15):
                    continue
                if selected_half == '16-end' and not (16 <= day <= 31):
                    continue
            elif filter_type == 'CUSTOM':
                if custom_start and custom_end:
                    if not (custom_start <= log_date <= custom_end):
                        continue
                else:
                    pass
        except Exception:
            continue

        filtered_logs.append(log)

    period_start = None
    period_end = None
    if filter_type in ('MONTHLY', 'WEEKLY', 'HALF'):
        try:
            year, month = (int(value) for value in selected_month.split('-', 1))
            month_last_day = calendar.monthrange(year, month)[1]
            start_day, end_day = (1, month_last_day)
            if filter_type == 'WEEKLY':
                start_day, end_day = (int(value) for value in selected_week.split('-', 1))
                end_day = min(end_day, month_last_day)
            elif filter_type == 'HALF':
                if selected_half == '1-15':
                    start_day, end_day = (1, 15)
                else:
                    start_day, end_day = (16, month_last_day)
            period_start = f'{year:04d}-{month:02d}-{start_day:02d}'
            period_end = f'{year:04d}-{month:02d}-{end_day:02d}'
        except (TypeError, ValueError):
            pass
    elif filter_type == 'CUSTOM':
        period_start = custom_start or None
        period_end = custom_end or None

    def paid_date_ranges(worker_id):
        return [
            (record.period_start, record.period_end)
            for record in SalaryPayment.query.filter_by(
                worker_id=worker_id,
                payout_portal=payout_portal
            ).all()
            if record.period_start and record.period_end
        ]

    def is_date_already_paid(date_value, paid_ranges):
        date_value = str(date_value or '')
        return any(start <= date_value <= end for start, end in paid_ranges)

    def is_period_fully_paid(start_date, end_date, paid_ranges):
        if not start_date or not end_date:
            return False
        uncovered_start = datetime.strptime(start_date, '%Y-%m-%d').date()
        required_end = datetime.strptime(end_date, '%Y-%m-%d').date()
        for paid_start, paid_end in sorted(paid_ranges):
            paid_start = datetime.strptime(paid_start, '%Y-%m-%d').date()
            paid_end = datetime.strptime(paid_end, '%Y-%m-%d').date()
            if paid_end < uncovered_start:
                continue
            if paid_start > uncovered_start:
                return False
            if paid_end >= required_end:
                return True
            uncovered_start = paid_end + timedelta(days=1)
        return False

    def attendance_rows_for_payroll(attendance_query, paid_ranges):
        all_rows = attendance_query.all()
        unpaid_rows = [
            row for row in all_rows
            if not is_date_already_paid(row.date, paid_ranges)
        ]
        if unpaid_rows or not is_period_fully_paid(period_start, period_end, paid_ranges):
            return unpaid_rows
        return all_rows

    worker_totals = {}
    if payout_portal == 'per_day':
        per_day_workers = Worker.query.filter(
            func.upper(func.trim(Worker.employment_type)) == 'PER DAY'
        )
        if selected_department:
            per_day_workers = per_day_workers.filter(func.lower(func.trim(Worker.department)) == selected_department.lower())
        per_day_workers = per_day_workers.order_by(Worker.name.asc()).all()

        for worker in per_day_workers:
            paid_ranges = paid_date_ranges(worker.id)
            attendance_query = DailyAttendance.query.filter_by(worker_id=worker.id)
            if period_start:
                attendance_query = attendance_query.filter(DailyAttendance.date >= period_start)
            if period_end:
                attendance_query = attendance_query.filter(DailyAttendance.date <= period_end)
            attendance_rows = attendance_rows_for_payroll(attendance_query, paid_ranges)
            if not attendance_rows:
                continue

            hourly_rate = float(worker.salary or 0.0) / 8.0
            present_days = sum(row.status == 'P' for row in attendance_rows)
            late_hours = sum(float(row.late_hours or 0.0) for row in attendance_rows)
            early_hours = sum(float(row.early_hours or 0.0) for row in attendance_rows)
            overtime_hours = payroll_overtime_hours(attendance_rows)
            night_hours = sum(float(row.night_hours or 0.0) for row in attendance_rows)
            worker_totals[worker.name] = (
                present_days * float(worker.salary or 0.0)
                - (late_hours + early_hours) * hourly_rate
                + (overtime_hours + night_hours) * hourly_rate
            )
    elif payout_portal != 'salaried':
        wage_logs = {}
        for log in filtered_logs:
            worker_name = (str(log.worker or '')).strip()
            worker = Worker.query.filter(func.lower(func.trim(Worker.name)) == worker_name.lower()).first()
            if not worker or (worker.employment_type or '').strip().lower().replace(' ', '_') != payout_portal:
                continue
            if selected_department and (worker.department or '').strip().lower() != selected_department.lower():
                continue
            wage_logs.setdefault(worker.id, {'worker': worker, 'logs': []})['logs'].append(log)

        for wage_data in wage_logs.values():
            worker = wage_data['worker']
            for log in wage_data['logs']:
                rate = get_rate_for_log(log)
                worker_totals[worker.name.strip()] = worker_totals.get(worker.name.strip(), 0) + ((log.pcs or 0) * rate)
    else:
        salaried_workers = Worker.query.filter(func.upper(func.trim(Worker.employment_type)) == 'SALARIED')
        if selected_department:
            salaried_workers = salaried_workers.filter(func.lower(func.trim(Worker.department)) == selected_department.lower())
        salaried_workers = salaried_workers.order_by(Worker.name.asc()).all()
        period_start = None
        period_end = None
        days_in_salary_month = None
        try:
            year, month = (int(value) for value in selected_month.split('-', 1))
            days_in_salary_month = calendar.monthrange(year, month)[1]
            period_start = f'{year:04d}-{month:02d}-01'
            period_end = f'{year:04d}-{month:02d}-{days_in_salary_month:02d}'
            if filter_type == 'WEEKLY':
                start_day, end_day = (int(value) for value in selected_week.split('-', 1))
                period_start = f'{year:04d}-{month:02d}-{start_day:02d}'
                period_end = f'{year:04d}-{month:02d}-{min(end_day, days_in_salary_month):02d}'
            elif filter_type == 'HALF':
                if selected_half == '1-15':
                    period_start = f'{year:04d}-{month:02d}-01'
                    period_end = f'{year:04d}-{month:02d}-15'
                else:
                    period_start = f'{year:04d}-{month:02d}-16'
                    period_end = f'{year:04d}-{month:02d}-{days_in_salary_month:02d}'
        except (TypeError, ValueError):
            pass
        if filter_type == 'CUSTOM':
            period_start = custom_start or None
            period_end = custom_end or None

        for worker in salaried_workers:
            paid_ranges = paid_date_ranges(worker.id)
            attendance_query = DailyAttendance.query.filter_by(worker_id=worker.id)
            if period_start:
                attendance_query = attendance_query.filter(DailyAttendance.date >= period_start)
            if period_end:
                attendance_query = attendance_query.filter(DailyAttendance.date <= period_end)
            attendance_rows = attendance_rows_for_payroll(attendance_query, paid_ranges)
            if not attendance_rows or not days_in_salary_month:
                worker_totals[worker.name] = 0.0
                continue

            salary = float(worker.salary or 0.0)
            allowance = float(worker.attendance_allowance or 0.0)
            monthly_salary = salary + allowance
            hourly_rate = monthly_salary / days_in_salary_month / 8.0
            present_days = sum(row.status == 'P' for row in attendance_rows)
            late_hours = sum(float(row.late_hours or 0.0) for row in attendance_rows)
            early_hours = sum(float(row.early_hours or 0.0) for row in attendance_rows)
            overtime_hours = payroll_overtime_hours(attendance_rows)
            night_hours = sum(float(row.night_hours or 0.0) for row in attendance_rows)
            worker_totals[worker.name] = (
                present_days * monthly_salary / days_in_salary_month
                - (late_hours + early_hours) * hourly_rate
                + (overtime_hours + night_hours) * hourly_rate
            )

    payout_data = []
    for worker, amount in sorted(worker_totals.items()):
        advance_total, advance_entries = get_worker_advance_summary(worker)
        worker_record = Worker.query.filter(
            func.lower(func.trim(Worker.name)) == str(worker).strip().lower()
        ).first()
        paid_ranges = paid_date_ranges(worker_record.id) if worker_record else []
        is_paid = is_period_fully_paid(period_start, period_end, paid_ranges)
        payout_item = {
            'name': worker,
            'worker_id': worker_record.id if worker_record else None,
            'amount': round(amount, 2),
            'gross_amount': round(amount, 2),
            'adv': round(advance_total, 2),
            'bal': round(amount - advance_total, 2),
            'advance_entries': advance_entries,
            'is_paid': is_paid,
        }
        if payout_portal in ('salaried', 'per_day'):
            worker_record = Worker.query.filter(
                func.lower(func.trim(Worker.name)) == str(worker).strip().lower()
            ).first()
            attendance_query = DailyAttendance.query.filter_by(worker_id=worker_record.id) if worker_record else DailyAttendance.query.filter(False)
            if payout_portal == 'salaried':
                attendance_query = attendance_query.filter(
                    DailyAttendance.date >= (period_start or '0000-01-01'),
                    DailyAttendance.date <= (period_end or '9999-12-31')
                )
            elif period_start:
                attendance_query = attendance_query.filter(DailyAttendance.date >= period_start)
                if period_end:
                    attendance_query = attendance_query.filter(DailyAttendance.date <= period_end)
            attendance_rows = attendance_rows_for_payroll(attendance_query, paid_ranges)
            payout_item.update({
                'present_days': sum(row.status == 'P' for row in attendance_rows),
                'absent_days': sum(row.status == 'A' for row in attendance_rows),
                'holiday_days': sum(row.status == 'H' for row in attendance_rows),
                'late_hours': sum(float(row.late_hours or 0.0) for row in attendance_rows),
                'early_hours': sum(float(row.early_hours or 0.0) for row in attendance_rows),
                'overtime_hours': payroll_overtime_hours(attendance_rows),
                'night_hours': sum(float(row.night_hours or 0.0) for row in attendance_rows),
            })
        if worker_record:
            payout_item['designation'] = worker_record.sub_designation or worker_record.role or ''

        if payout_portal in ('per_day', 'salaried') and worker_record:
            salary = float(worker_record.salary or 0.0)
            allowance = float(worker_record.attendance_allowance or 0.0)
            monthly_salary = salary + allowance
            total_days = calendar.monthrange(
                int(selected_month[:4]), int(selected_month[5:7])
            )[1] if len(selected_month) >= 7 else 0
            if payout_portal == 'salaried':
                gross_amount = payout_item['present_days'] * (monthly_salary / total_days) if total_days else 0.0
                per_hour_salary = monthly_salary / total_days / 8.0 if total_days else 0.0
            else:
                gross_amount = payout_item['present_days'] * monthly_salary
                per_hour_salary = monthly_salary / 8.0
            adjustment_amount = (
                -(
                    payout_item['late_hours'] + payout_item['early_hours']
                ) * per_hour_salary
                + (
                    payout_item['overtime_hours'] + payout_item['night_hours']
                ) * per_hour_salary
            )
            calculated_amount = gross_amount + adjustment_amount
            lower_amount = int(calculated_amount // 10) * 10
            upper_amount = lower_amount + 10
            rounded_amount = lower_amount if calculated_amount - lower_amount <= 5 else upper_amount
            payout_item.update({
                'salary': salary,
                'allowance': allowance,
                'monthly_salary': monthly_salary,
                'total_days': total_days,
                'gross_amount': gross_amount,
                'adjustment_amount': adjustment_amount,
                'per_hour_salary': per_hour_salary,
                'round_off_amount': rounded_amount - calculated_amount,
                'amount': round(rounded_amount, 2),
                'bal': round(rounded_amount - payout_item['adv'], 2),
            })
        payout_data.append(payout_item)

    period_label = 'DATE RANGE'
    month_label = ''
    try:
        month_label = datetime.strptime(selected_month, '%Y-%m').strftime('%b %Y').upper()
    except (TypeError, ValueError):
        month_label = ''

    if filter_type == 'MONTHLY':
        period_label = month_label or 'DATE RANGE'
    elif filter_type == 'WEEKLY':
        period_label = f'({selected_week}) {month_label}' if month_label else (selected_week or 'DATE RANGE')
    elif filter_type == 'HALF':
        if selected_half == '1-15':
            period_label = f'(1-15) {month_label}' if month_label else '(1-15)'
        elif selected_half == '16-end':
            period_label = f'(16-MONTH END) {month_label}' if month_label else '(16-MONTH END)'
    elif filter_type == 'CUSTOM':
        if custom_start and custom_end:
            try:
                start_dt = datetime.strptime(custom_start, '%Y-%m-%d')
                end_dt = datetime.strptime(custom_end, '%Y-%m-%d')
                period_label = f'({start_dt.strftime("%d-%m-%Y")} - {end_dt.strftime("%d-%m-%Y")}) {month_label}' if month_label else f'({start_dt.strftime("%d-%m-%Y")} - {end_dt.strftime("%d-%m-%Y")})'
            except (TypeError, ValueError):
                period_label = f'({custom_start} - {custom_end})'

    return render_template(
        'payout_sheet.html',
        payout_data=payout_data,
        selected_month=selected_month,
        selected_week=selected_week,
        selected_half=selected_half,
        period_label=period_label,
        selected_job=selected_job,
        logs=filtered_logs,
        rates=get_rates_dict(),
        current_filter=filter_type,
        custom_start=custom_start,
        custom_end=custom_end,
        payout_portal=payout_portal,
        available_payout_portals=available_payout_portals,
        selected_department=selected_department,
        departments=department_list
    )



def get_next_worker_code():
    try:
        codes = [int(code) for code, in Worker.query.with_entities(Worker.worker_code).all() if code and code.isdigit()]
        if codes:
            return str(max(codes, default=2000) + 1)
    except Exception:
        pass
    return '2001'


@app.route('/manager/departments', methods=['GET', 'POST'])
def departments():
    if session.get('role') not in ('owner', 'manager', 'assistant_manager'):
        return redirect(url_for('index'))

    if request.method == 'POST':
        if is_read_only_profile() and any(request.form.get(field) for field in (
            'delete_department_id', 'add_store_room_department_id', 'delete_store_room_id',
        )):
            return reject_read_only_edit('This profile has read-only access to departments and store rooms.')
        if request.form.get('delete_store_room_id'):
            store_room = DepartmentStoreRoom.query.get(request.form.get('delete_store_room_id'))
            if store_room:
                if AccessoryStorageLocation.query.filter_by(
                    department=store_room.department.name,
                    room=store_room.name,
                ).first():
                    flash('This store room is assigned to accessory stock and cannot be deleted.', 'danger')
                    return redirect(url_for('departments'))
                db.session.delete(store_room)
                db.session.commit()
                flash('Store room deleted successfully.', 'success')
            return redirect(url_for('departments'))
        if request.form.get('add_store_room_department_id'):
            department = Department.query.get(request.form.get('add_store_room_department_id'))
            name = (request.form.get('store_room_name') or '').strip()
            if not department:
                flash('Choose a valid department for the store room.', 'danger')
                return redirect(url_for('departments'))
            if not name:
                flash('Please enter a store room name.', 'danger')
                return redirect(url_for('departments'))
            if DepartmentStoreRoom.query.filter(
                DepartmentStoreRoom.department_id == department.id,
                func.lower(func.trim(DepartmentStoreRoom.name)) == name.casefold(),
            ).first():
                flash('This store room already exists in the selected department.', 'danger')
                return redirect(url_for('departments'))
            db.session.add(DepartmentStoreRoom(department_id=department.id, name=name))
            db.session.commit()
            flash(f'Store room added to {department.name}.', 'success')
            return redirect(url_for('departments'))
        if request.form.get('delete_department_id'):
            department = Department.query.get(request.form.get('delete_department_id'))
            if department:
                db.session.delete(department)
                db.session.commit()
                flash('Department deleted successfully.', 'success')
            return redirect(url_for('departments'))

        department_id = request.form.get('department_id', type=int)
        name = (request.form.get('name') or '').strip()
        if not name:
            flash('Please enter a department name.', 'danger')
            return redirect(url_for('departments'))

        department = Department.query.get(department_id) if department_id else None
        if department_id and not department:
            flash('Department not found.', 'danger')
            return redirect(url_for('departments'))
        duplicate_query = Department.query.filter(
            func.lower(func.trim(Department.name)) == name.casefold()
        )
        if department:
            duplicate_query = duplicate_query.filter(Department.id != department.id)
        if duplicate_query.first():
            flash('This department already exists.', 'danger')
            return redirect(url_for('departments'))
        if department:
            department.name = name
            db.session.commit()
            flash('Department updated successfully.', 'success')
            return redirect(url_for('departments'))

        db.session.add(Department(name=name))
        db.session.commit()
        flash('Department added successfully.', 'success')
        return redirect(url_for('departments'))

    editing_department = Department.query.get(request.args.get('edit_id', type=int)) if request.args.get('edit_id') else None
    department_list = Department.query.order_by(func.lower(Department.name)).all()
    return render_template('departments.html', departments=department_list, editing_department=editing_department)


@app.route('/manager/workers/<job_no>', methods=['GET', 'POST'], endpoint='workers')
@app.route('/manager/workers', methods=['GET', 'POST'])
def workers(job_no=None):
    if not session.get('role'):
        return redirect(url_for('index'))

    if request.method == 'POST':
        # Get form data
        worker_id = request.form.get('worker_id')
        name = request.form.get('name')
        email = request.form.get('email')
        phone = request.form.get('phone')
        whatsapp_number = request.form.get('whatsapp_number')
        emergency_number = request.form.get('emergency_number')
        blood_group = request.form.get('blood_group')
        age = request.form.get('age') or None
        cnic = request.form.get('cnic')
        role = request.form.get('role')
        dob = request.form.get('dob')
        gender = request.form.get('gender')
        marital_status = request.form.get('marital_status')
        nationality = request.form.get('nationality')
        address = request.form.get('address')
        city = request.form.get('city')
        state = request.form.get('state')
        zip_code = request.form.get('zip_code')
        supervisor = request.form.get('supervisor')
        sub_designation = request.form.get('sub_designation')
        joining_date = request.form.get('joining_date')
        referred_by = request.form.get('referred_by')
        hired_by = request.form.get('hired_by')
        salary = request.form.get('salary') or None
        attendance_allowance = request.form.get('attendance_allowance') or None
        hod = request.form.get('hod')
        employment_type = request.form.get('employment_type')
        department = request.form.get('department')
        status = (request.form.get('status') or 'Active').strip()
        if status not in ('Active', 'Non-active'):
            flash('Please select a valid worker status.', 'danger')
            return redirect(url_for('workers'))
        calculated_age = None
        if dob:
            try:
                birth_date = datetime.strptime(dob, '%Y-%m-%d').date()
                today = datetime.now().date()
                calculated_age = today.year - birth_date.year - ((today.month, today.day) < (birth_date.month, birth_date.day))
                if calculated_age < 0:
                    calculated_age = None
            except ValueError:
                calculated_age = None

        edu_degrees = request.form.getlist('edu_degree[]')
        edu_fields = request.form.getlist('edu_field[]')
        edu_institutions = request.form.getlist('edu_institution[]')
        edu_completions = request.form.getlist('edu_completion[]')

        picture_filename = None
        image_file = request.files.get('picture')
        if image_file and image_file.filename:
            filename = secure_filename(image_file.filename)
            save_path = os.path.join(app.config['UPLOAD_FOLDER'], filename)
            image_file.save(save_path)
            picture_filename = filename

        if worker_id:
            # Update existing
            w = Worker.query.get(worker_id)
            if not w:
                flash('Worker not found.', 'danger')
                return redirect(url_for('workers'))
            w.name = name
            if email is not None:
                w.email = email
            w.phone = phone
            w.whatsapp_number = whatsapp_number
            w.emergency_number = emergency_number
            w.blood_group = blood_group
            w.age = calculated_age
            w.cnic = cnic
            w.role = role
            w.dob = dob
            w.gender = gender
            w.marital_status = marital_status
            w.nationality = nationality
            w.address = address
            w.city = city
            if zip_code is not None:
                w.zip_code = zip_code
            w.supervisor = supervisor
            w.sub_designation = sub_designation
            w.joining_date = joining_date
            w.referred_by = referred_by
            w.hired_by = hired_by
            w.salary = float(salary) if salary else None
            w.attendance_allowance = float(attendance_allowance) if attendance_allowance else None
            w.hod = hod
            w.employment_type = employment_type
            w.department = department
            w.status = status
            if picture_filename:
                w.picture = picture_filename

            EducationBackground.query.filter_by(worker_id=w.id).delete()
            for degree, field_of_study, institution, completion_date in zip(edu_degrees, edu_fields, edu_institutions, edu_completions):
                if degree.strip() or field_of_study.strip() or institution.strip() or completion_date.strip():
                    db.session.add(EducationBackground(
                        worker_id=w.id,
                        degree=degree.strip(),
                        field_of_study=field_of_study.strip(),
                        institution=institution.strip(),
                        completion_date=completion_date.strip()
                    ))

            db.session.commit()
            flash('Worker updated successfully.', 'success')
            return redirect(url_for('workers', new_entry='1'))

        # Create and save new worker record
        new_worker = Worker(
            name=name,
            email=email,
            phone=phone,
            whatsapp_number=whatsapp_number,
            emergency_number=emergency_number,
            blood_group=blood_group,
            picture=picture_filename,
            age=calculated_age,
            worker_code=get_next_worker_code(),
            cnic=cnic,
            role=role,
            dob=dob,
            gender=gender,
            marital_status=marital_status,
            nationality=nationality,
            address=address,
            city=city,
            state=state,
            zip_code=zip_code,
            supervisor=supervisor,
            sub_designation=sub_designation,
            joining_date=joining_date,
            referred_by=referred_by,
            hired_by=hired_by,
            salary=float(salary) if salary else None,
            attendance_allowance=float(attendance_allowance) if attendance_allowance else None,
            hod=hod,
            employment_type=employment_type,
            department=department,
            status=status
        )
        db.session.add(new_worker)
        db.session.flush()
        for degree, field_of_study, institution, completion_date in zip(edu_degrees, edu_fields, edu_institutions, edu_completions):
            if degree.strip() or field_of_study.strip() or institution.strip() or completion_date.strip():
                db.session.add(EducationBackground(
                    worker_id=new_worker.id,
                    degree=degree.strip(),
                    field_of_study=field_of_study.strip(),
                    institution=institution.strip(),
                    completion_date=completion_date.strip()
                ))
        db.session.commit()

        flash('Worker added successfully.', 'success')
        return redirect(url_for('workers'))

    # Fetch all workers
    # support editing/prefill via query param
    editing_worker = None
    new_entry = request.args.get('new_entry') == '1'
    query_worker_id = None if new_entry else (request.args.get('worker_id') or request.args.get('edit_id'))
    if query_worker_id:
        try:
            editing_worker = Worker.query.get(int(query_worker_id))
        except Exception:
            editing_worker = None

    workers_list = Worker.query.order_by(Worker.id.desc()).all()
    advance_summaries = []
    for worker in workers_list:
        advance_entries = [a for a in worker.advances if a.record_type == 'advance']
        if not advance_entries:
            continue
        total_advance = sum(
            (a.amount or 0) if a.record_type == 'advance' else -(a.amount or 0)
            for a in worker.advances
        )
        if total_advance <= 0:
            continue
        month_map = {}
        for entry in advance_entries:
            date_value = (entry.date or '').strip()
            if not date_value:
                continue
            try:
                parsed = datetime.strptime(date_value, '%Y-%m-%d')
                key = parsed.strftime('%Y-%m')
                month_map[key] = parsed.strftime('%b %Y')
            except Exception:
                key = date_value[:7]
                month_map[key] = date_value
        months = ', '.join([month_map[key] for key in sorted(month_map.keys())]) if month_map else '-' 
        advance_summaries.append({
            'worker': worker,
            'total_advance': total_advance,
            'months': months
        })
    next_worker_code = get_next_worker_code() if not editing_worker else None
    department_list = Department.query.order_by(func.lower(Department.name)).all()
    return render_template('workers.html', workers=workers_list, editing_worker=editing_worker, new_entry=new_entry, next_worker_code=next_worker_code, advance_summaries=advance_summaries, departments=department_list)


@app.route('/manager/worker/<int:worker_id>/print')
def worker_print(worker_id):
    if not session.get('role'):
        return redirect(url_for('index'))
    worker = Worker.query.get(worker_id)
    if not worker:
        flash('Worker not found.', 'danger')
        return redirect(url_for('workers'))
    return render_template('worker_print.html', worker=worker)


@app.route('/manager/worker-advance', methods=['GET', 'POST'])
def worker_advance():
    if not session.get('role'):
        return redirect(url_for('index'))

    search = request.args.get('q', '').strip()
    selected_worker_id = request.args.get('worker_id')
    selected_worker = None
    advances = []
    balance = 0

    workers_query = Worker.query
    if search:
        term = f"%{search}%"
        workers_query = workers_query.filter(
            or_(
                Worker.name.ilike(term),
                Worker.phone.ilike(term),
                Worker.worker_code.ilike(term),
                Worker.cnic.ilike(term)
            )
        )
    workers = workers_query.order_by(Worker.id.desc()).all()

    if request.args.get('format') == 'json':
        return jsonify({
            'selected_worker_id': selected_worker_id or None,
            'workers': [
                {
                    'id': worker.id,
                    'name': worker.name or '-',
                    'worker_code': worker.worker_code or '-',
                    'phone': worker.phone or '-',
                    'cnic': worker.cnic or '-',
                    'select_url': url_for('worker_advance', worker_id=worker.id, q=search),
                }
                for worker in workers
            ],
        })

    if selected_worker_id:
        selected_worker = Worker.query.get(int(selected_worker_id))
        if selected_worker:
            advances = WorkerAdvance.query.filter_by(worker_id=selected_worker.id).order_by(WorkerAdvance.date.desc(), WorkerAdvance.id.desc()).all()
            balance = sum([a.amount if a.record_type == 'advance' else -a.amount for a in advances])

    today = datetime.now().strftime('%Y-%m-%d')

    if request.method == 'POST':
        action = request.form.get('form_action')
        worker_id = request.form.get('worker_id')
        worker = Worker.query.get(worker_id)
        if worker:
            amount = float(request.form.get('amount') or 0)
            date = request.form.get('date') or datetime.now().strftime('%Y-%m-%d')
            note = request.form.get('note', '')
            if action == 'add_advance' and amount > 0:
                record = WorkerAdvance(worker_id=worker.id, amount=amount, date=date, record_type='advance', note=note)
                db.session.add(record)
                db.session.commit()
                flash('Advance recorded successfully.', 'success')
            elif action == 'remove_advance' and amount > 0:
                record = WorkerAdvance(worker_id=worker.id, amount=amount, date=date, record_type='payment', note=note)
                db.session.add(record)
                db.session.commit()
                flash('Advance payment recorded successfully.', 'success')
        return redirect(url_for('worker_advance', worker_id=worker_id, q=search))

    return render_template(
        'worker_advance.html',
        workers=workers,
        selected_worker=selected_worker,
        advances=advances,
        balance=balance,
        search=search,
        today=today
    )


def attendance_years():
    years = {datetime.now().year}
    years.update(record.year for record in Attendance.query.with_entities(Attendance.year).all())
    return sorted(years, reverse=True)


def parse_attendance_number(value, label, allow_decimal=False):
    raw_value = (value or '').strip()
    if not raw_value:
        raise ValueError(f'{label} is required.')
    try:
        parsed = float(raw_value) if allow_decimal else int(raw_value)
    except (TypeError, ValueError):
        raise ValueError(f'{label} must be a valid number.')
    if parsed < 0:
        raise ValueError(f'{label} cannot be negative.')
    return parsed


def pakistan_public_holidays(year):
    fixed_holidays = {
        (2, 5): 'Kashmir Solidarity Day',
        (3, 23): 'Pakistan Day',
        (5, 1): 'Labour Day',
        (5, 28): 'Youm-e-Takbeer',
        (8, 14): 'Independence Day',
        (9, 6): 'Defence Day',
        (11, 9): 'Allama Iqbal Day',
        (12, 25): 'Quaid-e-Azam Day / Christmas Day',
    }
    return {
        f'{year:04d}-{month:02d}-{day:02d}': name
        for (month, day), name in fixed_holidays.items()
    }


def payroll_overtime_hours(attendance_rows):
    overtime_total = 0.0
    holidays_by_year = {}
    for row in attendance_rows:
        overtime_hours = float(row.overtime_hours or 0.0)
        date_value = str(row.date or '')
        try:
            attendance_date = datetime.strptime(date_value, '%Y-%m-%d').date()
        except ValueError:
            overtime_total += overtime_hours
            continue

        if attendance_date.year not in holidays_by_year:
            holidays_by_year[attendance_date.year] = pakistan_public_holidays(attendance_date.year)
        if attendance_date.weekday() == calendar.SUNDAY or date_value in holidays_by_year[attendance_date.year]:
            overtime_hours *= 2
        overtime_total += overtime_hours
    return overtime_total


@app.route('/worker-attendance', methods=['GET', 'POST'])
def worker_attendance():
    if session.get('role') not in ('owner', 'manager', 'assistant_manager'):
        return redirect(url_for('index'))

    current_date = datetime.now()
    # Worker attendance is for workers whose pay is based on attendance.
    attendance_portal = 'salaried'
    attendance_employment_types = ('SALARIED', 'PER DAY')
    attendance_role = None
    search = (request.args.get('q') or request.form.get('q') or '').strip()
    try:
        selected_year = int(request.args.get('year') or request.form.get('year') or current_date.year)
        selected_month = int(request.args.get('month') or request.form.get('month') or current_date.month)
    except ValueError:
        selected_year, selected_month = current_date.year, current_date.month
    selected_year = max(2000, min(selected_year, current_date.year + 1))
    selected_month = selected_month if 1 <= selected_month <= 12 else current_date.month
    if selected_year == current_date.year and selected_month > current_date.month:
        selected_month = current_date.month
    selected_worker_id = request.args.get('worker_id') or request.form.get('worker_id')
    selected_worker = Worker.query.get(int(selected_worker_id)) if selected_worker_id and str(selected_worker_id).isdigit() else None
    if selected_worker and attendance_portal == 'salaried' and (selected_worker.employment_type or '').strip().upper() not in attendance_employment_types:
        selected_worker = None
    elif selected_worker and attendance_role and (selected_worker.role or '').upper() != attendance_role:
        selected_worker = None

    if request.method == 'POST':
        try:
            selected_worker = Worker.query.get(int(request.form.get('worker_id')))
            if not selected_worker:
                raise ValueError('Please select a valid worker.')
            if attendance_portal == 'salaried' and (selected_worker.employment_type or '').strip().upper() not in attendance_employment_types:
                raise ValueError('Selected worker does not belong to this attendance portal.')
            if attendance_role and (selected_worker.role or '').upper() != attendance_role:
                raise ValueError('Selected worker does not belong to this attendance portal.')
            selected_year = int(request.form.get('year'))
            selected_month = int(request.form.get('month'))
            if selected_month < 1 or selected_month > 12:
                raise ValueError('Please select a valid attendance month.')
            is_per_day_worker = (selected_worker.employment_type or '').strip().upper() == 'PER DAY'
            public_holiday_dates = pakistan_public_holidays(selected_year)
            days_in_month = calendar.monthrange(selected_year, selected_month)[1]
            daily_rows = []
            for day in range(1, days_in_month + 1):
                date_value = f'{selected_year:04d}-{selected_month:02d}-{day:02d}'
                status = (request.form.get(f'attendance_status_{day}') or 'P').strip().upper()
                is_special_day = (
                    date_value in public_holiday_dates
                    or calendar.weekday(selected_year, selected_month, day) == calendar.SUNDAY
                )
                if is_per_day_worker and is_special_day:
                    status = 'A'
                if status not in ('P', 'A', 'H'):
                    raise ValueError('Attendance status must be P, A, or H.')
                late_hours = parse_attendance_number(request.form.get(f'late_hours_{day}') or '0', 'Late hours', allow_decimal=True)
                early_hours = parse_attendance_number(request.form.get(f'early_hours_{day}') or '0', 'Early hours', allow_decimal=True)
                overtime_hours = parse_attendance_number(request.form.get(f'overtime_hours_{day}') or '0', 'Overtime hours', allow_decimal=True)
                daily_rows.append({
                    'date': date_value,
                    'status': status,
                    'late_hours': late_hours,
                    'early_hours': early_hours,
                    'overtime_hours': overtime_hours,
                    'night_hours': parse_attendance_number(request.form.get(f'daily_night_hours_{day}') or request.form.get(f'night_hours_{day}') or '0', 'Night hours', allow_decimal=True),
                })
            factory_days = days_in_month
            absent_days = sum(row['status'] == 'A' for row in daily_rows)
            present_days = sum(row['status'] == 'P' for row in daily_rows)
            overtime = sum(row['overtime_hours'] for row in daily_rows)
            early_leave = sum(row['early_hours'] for row in daily_rows)
            night = sum(row['night_hours'] for row in daily_rows)
            late_days = sum(row['late_hours'] > 0 for row in daily_rows)
            on_time_days = factory_days - late_days
            new_daily_records = 0
            for row in daily_rows:
                daily_record = DailyAttendance.query.filter_by(worker_id=selected_worker.id, date=row['date']).first()
                if daily_record and is_read_only_profile():
                    continue
                if not daily_record:
                    daily_record = DailyAttendance(worker_id=selected_worker.id, date=row['date'])
                    db.session.add(daily_record)
                    new_daily_records += 1
                daily_record.status = row['status']
                daily_record.late_hours = row['late_hours']
                daily_record.early_hours = row['early_hours']
                daily_record.overtime_hours = row['overtime_hours']
                daily_record.night_hours = row['night_hours']
            if is_read_only_profile() and not new_daily_records:
                flash('All attendance dates in this month are already saved.', 'warning')
                return redirect(url_for('worker_attendance', worker_id=selected_worker.id, year=selected_year, month=selected_month, portal=attendance_portal))
            saved_daily_records = DailyAttendance.query.filter(
                DailyAttendance.worker_id == selected_worker.id,
                DailyAttendance.date >= f'{selected_year:04d}-{selected_month:02d}-01',
                DailyAttendance.date <= f'{selected_year:04d}-{selected_month:02d}-{days_in_month:02d}',
            ).all()
            absent_days = sum(row.status == 'A' for row in saved_daily_records)
            present_days = sum(row.status == 'P' for row in saved_daily_records)
            overtime = sum(float(row.overtime_hours or 0) for row in saved_daily_records)
            early_leave = sum(float(row.early_hours or 0) for row in saved_daily_records)
            night = sum(float(row.night_hours or 0) for row in saved_daily_records)
            late_days = sum(float(row.late_hours or 0) > 0 for row in saved_daily_records)
            on_time_days = days_in_month - late_days
            record = Attendance.query.filter_by(worker_id=selected_worker.id, year=selected_year, month=selected_month).first()
            if not record:
                record = Attendance(worker_id=selected_worker.id, year=selected_year, month=selected_month)
                db.session.add(record)
            record.factory_operating_days = factory_days
            record.absent_days = absent_days
            record.present_days = present_days
            record.overtime_hours = overtime
            record.early_leave_hours = early_leave
            record.night_hours = night
            record.late_days = late_days
            record.on_time_days = on_time_days
            db.session.commit()
            flash('Attendance saved successfully.', 'success')
            return redirect(url_for('worker_attendance', worker_id=selected_worker.id, year=selected_year, month=selected_month, portal=attendance_portal))
        except (ValueError, TypeError) as exc:
            db.session.rollback()
            flash(str(exc), 'danger')

    workers_query = Worker.query
    if attendance_portal:
        if attendance_portal == 'salaried':
            workers_query = workers_query.filter(
                func.upper(func.trim(Worker.employment_type)).in_(attendance_employment_types)
            )
        else:
            workers_query = workers_query.filter(func.upper(Worker.role) == attendance_role)
    if search:
        term = f'%{search}%'
        workers_query = workers_query.filter(or_(
            Worker.name.ilike(term),
            Worker.worker_code.ilike(term),
            Worker.employment_type.ilike(term),
            Worker.role.ilike(term),
            Worker.sub_designation.ilike(term),
            Worker.phone.ilike(term),
            Worker.cnic.ilike(term),
            func.cast(Worker.age, String).ilike(term),
            func.cast(Worker.id, String).ilike(term),
        ))
    workers = workers_query.order_by(Worker.name.asc()).limit(50).all()
    existing = Attendance.query.filter_by(worker_id=selected_worker.id, year=selected_year, month=selected_month).first() if selected_worker else None
    history = Attendance.query.filter_by(worker_id=selected_worker.id).order_by(Attendance.year.desc(), Attendance.month.desc()).all() if selected_worker else []
    yearly_records = Attendance.query.filter_by(worker_id=selected_worker.id, year=selected_year).order_by(Attendance.month.asc()).all() if selected_worker else []
    yearly_by_month = {record.month: record for record in yearly_records}
    yearly_daily_records = DailyAttendance.query.filter(
        DailyAttendance.worker_id == selected_worker.id,
        DailyAttendance.date >= f'{selected_year:04d}-01-01',
        DailyAttendance.date <= f'{selected_year:04d}-12-31'
    ).all() if selected_worker else []
    months_with_daily_records = {int(record.date[5:7]) for record in yearly_daily_records}
    yearly_overtime_hours = payroll_overtime_hours(yearly_daily_records) + sum(
        float(record.overtime_hours or 0.0)
        for record in yearly_records
        if record.month not in months_with_daily_records
    )
    daily_records = {
        record.date: record
        for record in DailyAttendance.query.filter(
            DailyAttendance.worker_id == selected_worker.id,
            DailyAttendance.date >= f'{selected_year:04d}-{selected_month:02d}-01',
            DailyAttendance.date <= f'{selected_year:04d}-{selected_month:02d}-{calendar.monthrange(selected_year, selected_month)[1]:02d}'
        ).all()
    } if selected_worker else {}
    yearly_summary = {
        'factory_days': sum(record.factory_operating_days for record in yearly_records),
        'present_days': sum(record.present_days for record in yearly_records),
        'absent_days': sum(record.absent_days for record in yearly_records),
        'overtime_hours': yearly_overtime_hours,
        'early_leave_hours': sum(record.early_leave_hours for record in yearly_records),
        'night_hours': sum(record.night_hours or 0 for record in yearly_records),
        'late_days': sum(record.late_days or 0 for record in yearly_records),
        'on_time_days': sum(record.on_time_days or 0 for record in yearly_records),
    }
    days_in_selected_month = calendar.monthrange(selected_year, selected_month)[1]
    holiday_dates = pakistan_public_holidays(selected_year)
    sunday_dates = {
        f'{selected_year:04d}-{selected_month:02d}-{day:02d}'
        for day in range(1, days_in_selected_month + 1)
        if calendar.weekday(selected_year, selected_month, day) == calendar.SUNDAY
    }
    month_options = [(number, calendar.month_name[number]) for number in range(1, 13)]
    if selected_year == current_date.year:
        month_options = month_options[:current_date.month]
    return render_template('worker_attendance.html', workers=workers, selected_worker=selected_worker, selected_year=selected_year, selected_month=selected_month, days_in_selected_month=days_in_selected_month, existing=existing, daily_records=daily_records, history=history, yearly_by_month=yearly_by_month, yearly_summary=yearly_summary, years=attendance_years(), months=month_options, search=search, readonly=is_read_only_profile(), attendance_portal=attendance_portal, holiday_dates=holiday_dates, sunday_dates=sunday_dates)


@app.route('/manager/delete-worker', methods=['POST'])
def delete_worker():
    if not session.get('role'):
        return redirect(url_for('index'))
    if session.get('role') not in ('owner', 'manager') or is_read_only_profile():
        return reject_read_only_edit('Only the owner and manager can delete worker profiles.')

    worker_id = request.form.get('worker_id')
    worker = Worker.query.get(worker_id) if worker_id else None

    if worker:
        # attempt to remove picture file
        if worker.picture:
            try:
                pic_path = os.path.join(app.config['UPLOAD_FOLDER'], worker.picture)
                if os.path.exists(pic_path):
                    os.remove(pic_path)
            except Exception:
                pass
        db.session.delete(worker)
        db.session.commit()
        flash('Worker deleted successfully.', 'success')
    else:
        flash('Worker not found.', 'danger')

    return redirect(url_for('workers'))



@app.route('/stock-portal')
def stock_portal():
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    fabric_totals = get_fabric_stock_totals()
    accessory_pending_po = SavedRequirement.query.filter(
        or_(SavedRequirement.accessory_status.is_(None), SavedRequirement.accessory_status == 'PENDING')
    ).count()
    ready_to_ship = 0
    shipped_awaiting_delivery = 0
    for order in Order.query.all():
        if not order.job_no:
            continue
        status = order.fulfillment_status or 'PENDING'
        if get_order_shipping_snapshot(order)['available_pcs'] > 0:
            ready_to_ship += 1
        elif status == 'SHIPPED':
            shipped_awaiting_delivery += 1
    return render_template(
        'stock_portal.html', fabric_totals=fabric_totals,
        accessory_summary=get_accessory_stock_summary(),
        accessory_pending_po=accessory_pending_po,
        ready_to_ship=ready_to_ship, shipped_awaiting_delivery=shipped_awaiting_delivery,
        show_fabric_report_sections='fabric_reports' in getattr(g, 'page_access_keys', set()),
    )



@app.route('/stock-portal/fabric-ledger')
def fabric_ledger():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    search = (request.args.get('search') or '').strip()
    quality_filter = (request.args.get('quality') or '').strip()
    supplier_filter = (request.args.get('supplier') or '').strip()
    status_filter = (request.args.get('status') or '').strip()
    sort_order = (request.args.get('sort_order') or 'asc').strip().lower()
    if sort_order not in {'asc', 'desc'}:
        sort_order = 'asc'
    if not status_filter:
        status_filter = ''

    status_options = [
        'Not Used',
        'Not Used / Rejected',
        'Not Used / Re-active',
        'Active',
        'Active / Rejected',
        'Active / Re-active',
        'Partially Used',
        'Partially Used / Rejected',
        'Partially Used / Re-active',
        'Finished',
        'Finished / Rejected',
        'Finished / Re-active',
    ]

    inventories = Inventory.query.filter(Inventory.serial_no.isnot(None)).order_by(Inventory.id.desc()).all()
    orders_by_job = {o.job_no: o for o in Order.query.all() if o.job_no}

    stock_rows = []
    totals = {'received': 0.0, 'issued': 0.0, 'balance': 0.0, 'rejected': 0.0, 'recovered': 0.0}
    by_quality, by_supplier, by_order = {}, {}, {}

    for inv in inventories:
        status = calculate_inventory_fabric_balances(inv)
        label = get_inventory_status(inv)
        order = orders_by_job.get(inv.order_id)
        quality = (inv.fabric_quality or 'UNSPECIFIED').strip().upper()
        supplier = (inv.suppliers or inv.received_from or 'UNKNOWN').strip().upper()

        if search:
            haystack = ' '.join([
                inv.serial_no or '', inv.order_id or '', quality, supplier,
                order.name if order else '', order.article_name if order else ''
            ]).lower()
            if search.lower() not in haystack:
                continue
        if quality_filter and quality != quality_filter:
            continue
        if supplier_filter and supplier != supplier_filter:
            continue
        if status_filter and label.casefold() != status_filter.casefold():
            continue

        row = {
            'serial_no': inv.serial_no, 'order_id': inv.order_id, 'order': order,
            'quality': quality, 'supplier': supplier, 'width': inv.width or 'â€”', 'recv_date': inv.recv_date,
            'received': status['total_fabric'], 'used': status['used_fabric'],
            'balance': status['left_over_fabric'], 'rejected': status['rejected_fabric'],
            'recovered': status['recovered_fabric'], 'status_label': label,
        }
        stock_rows.append(row)

        totals['received'] += row['received']; totals['issued'] += row['used']
        totals['balance'] += row['balance']; totals['rejected'] += row['rejected']
        totals['recovered'] += row['recovered']

        q = by_quality.setdefault(quality, {'received': 0.0, 'issued': 0.0, 'balance': 0.0, 'lots': 0})
        q['received'] += row['received']; q['issued'] += row['used']; q['balance'] += row['balance']; q['lots'] += 1

        s = by_supplier.setdefault(supplier, {'received': 0.0, 'issued': 0.0, 'balance': 0.0, 'lots': 0})
        s['received'] += row['received']; s['issued'] += row['used']; s['balance'] += row['balance']; s['lots'] += 1

        o = by_order.setdefault(inv.order_id or '-', {'order': order, 'received': 0.0, 'issued': 0.0, 'balance': 0.0, 'lots': 0})
        o['received'] += row['received']; o['issued'] += row['used']; o['balance'] += row['balance']; o['lots'] += 1

    stock_rows.sort(
        key=lambda r: (r['serial_no'] or '', r['order_id'] or ''),
        reverse=(sort_order == 'desc')
    )

    all_qualities = sorted({(inv.fabric_quality or 'UNSPECIFIED').strip().upper() for inv in inventories})
    all_suppliers = sorted({(inv.suppliers or inv.received_from or 'UNKNOWN').strip().upper() for inv in inventories})
    party_names = sorted({
        (party_name or '').strip()
        for (party_name,) in db.session.query(Article.party_name)
        .filter(Article.party_name.isnot(None), Article.party_name != '')
        .distinct()
        .all()
        if party_name and party_name.strip()
    })

    # Movement ledger: RECEIVED (from Inventory) + ISSUED (from InventoryRow, written when a cutting sheet uses fabric)
    movements = []

    def movement_timestamp(date_value, time_value='', fallback=None):
        parsed_date = normalize_date(date_value)
        if not parsed_date and isinstance(fallback, datetime):
            parsed_date = fallback
        if not parsed_date:
            return datetime.min, ''

        time_text = (time_value or '').strip()
        for time_format in ('%H:%M:%S', '%H:%M', '%I:%M:%S %p', '%I:%M %p', '%I:%M%p'):
            try:
                parsed_time = datetime.strptime(time_text, time_format).time()
                return parsed_date.replace(
                    hour=parsed_time.hour,
                    minute=parsed_time.minute,
                    second=parsed_time.second,
                ), parsed_time.strftime('%H:%M')
            except ValueError:
                continue

        if isinstance(fallback, datetime):
            return parsed_date.replace(
                hour=fallback.hour,
                minute=fallback.minute,
                second=fallback.second,
            ), fallback.strftime('%H:%M')
        return parsed_date, time_text

    for inv in inventories:
        received_qty = parse_numeric(inv.fabric_qty_a) + parse_numeric(inv.fabric_qty_b)
        received_at, received_time = movement_timestamp(inv.recv_date, fallback=inv.created_at)
        movements.append({
            'date': inv.recv_date, 'type': 'RECEIVED', 'serial_no': inv.serial_no,
            'order_id': inv.order_id, 'qty': received_qty,
            'used': 0.0, 'balance': received_qty,
            'reference': inv.challan_no or '-',
            'time': received_time, '_sort_at': received_at, '_sort_id': inv.id or 0,
        })
    inventory_by_id = {inv.id: inv for inv in inventories}
    issue_rows = InventoryRow.query.filter(
        InventoryRow.fabric_use.isnot(None),
        InventoryRow.fabric_use != '',
    ).order_by(InventoryRow.id.desc()).all()
    issue_serials = {row.sno.strip() for row in issue_rows if row.sno and row.sno.strip()}
    cutting_sheets = CuttingSheet.query.filter(
        CuttingSheet.serial_no.in_(issue_serials)
    ).all() if issue_serials else []
    cutting_sheet_by_key = {
        ((sheet.serial_no or '').strip(), (sheet.cut_no or '').strip()): sheet
        for sheet in cutting_sheets
    }
    for row in issue_rows:
        if not row.fabric_use:
            continue
        inv = inventory_by_id.get(row.inventory_id)
        cutting_sheet = cutting_sheet_by_key.get(((row.sno or '').strip(), (row.cut_no or '').strip()))
        movement_date = row.date or (cutting_sheet.cut_date if cutting_sheet else '')
        movement_time = cutting_sheet.time_field if cutting_sheet else ''
        issued_at, issued_time = movement_timestamp(
            movement_date,
            movement_time,
            cutting_sheet.created_at if cutting_sheet else None,
        )
        file_no = (row.file_no or inv.file_no if inv else '').strip()
        if file_no:
            file_no = file_no.replace('FILE-', '', 1).replace('file-', '', 1).strip()
            ref = f'FILE {file_no}/CUT {row.cut_no}' if row.cut_no else f'FILE {file_no}'
        elif row.cut_no:
            ref = f'CUT {row.cut_no}'
        else:
            ref = '-'
        movements.append({
            'date': movement_date, 'type': 'ISSUED', 'serial_no': inv.serial_no if inv else '-',
            'order_id': inv.order_id if inv else '-',
            'qty': parse_numeric(row.fabric_issue) or parse_numeric(row.fabric_use),
            'used': parse_numeric(row.fabric_use),
            'balance': parse_numeric(row.balance),
            'reference': ref,
            'time': issued_time, '_sort_at': issued_at, '_sort_id': row.id or 0,
        })
    movements.sort(key=lambda movement: (movement['_sort_at'], movement['_sort_id']), reverse=True)
    for movement in movements:
        movement.pop('_sort_at', None)
        movement.pop('_sort_id', None)

    return render_template(
        'fabric_ledger.html', stock_rows=stock_rows, totals=totals,
        by_quality=sorted(by_quality.items()), by_supplier=sorted(by_supplier.items()),
        by_order=sorted(by_order.items(), key=lambda item: item[0]),
        all_qualities=all_qualities, all_suppliers=all_suppliers,
        search=search, quality_filter=quality_filter, supplier_filter=supplier_filter,
        status_filter=status_filter, status_options=status_options, sort_order=sort_order, movements=movements, party_names=party_names,
        show_fabric_report_sections='fabric_reports' in getattr(g, 'page_access_keys', set()),
    )


@app.route('/stock-portal/fabric-position-summary')
def fabric_position_summary():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    party_name = (request.args.get('party_name') or '').strip()
    start_value = (request.args.get('start_date') or '').strip()
    end_value = (request.args.get('end_date') or '').strip()
    start_date = normalize_date(start_value).date() if normalize_date(start_value) else None
    end_date = normalize_date(end_value).date() if normalize_date(end_value) else None
    rows = []

    storage_key = 'party-article-consumption'
    saved_party_consumption = load_party_article_consumption()
    if not isinstance(saved_party_consumption, dict):
        saved_party_consumption = {}
    session[storage_key] = saved_party_consumption

    def normalize_party_key(value):
        return (value or '').strip().casefold()

    def make_article_key(article_label):
        normalized = re.sub(r'[^a-z0-9]+', '_', (article_label or '').lower()).strip('_')
        return normalized or 'article'

    def article_bucket_key(order):
        article_id = getattr(order, 'article_id', None)
        if article_id is not None:
            return f'id:{article_id}'
        label = (getattr(order, 'article', None) or getattr(order, 'article_name', None) or 'UNSPECIFIED').strip()
        return f'label:{" ".join(label.casefold().split())}'

    def get_saved_consumption_for_order(party_key_value, order, fallback_key):
        storage = saved_party_consumption.get(party_key_value, {}) if isinstance(saved_party_consumption, dict) else {}
        candidates = []
        if fallback_key:
            candidates.append(fallback_key)
        if order:
            for value in [
                getattr(order, 'article', None),
                getattr(order, 'article_name', None),
                (getattr(order, 'article_name', None) or getattr(order, 'article', None)),
            ]:
                if value:
                    candidates.append(make_article_key(value))
        seen = set()
        for candidate in candidates:
            if not candidate or candidate in seen:
                continue
            seen.add(candidate)
            if candidate in storage:
                return parse_numeric(storage.get(candidate, 0.0))
        if storage:
            values = [parse_numeric(v) for v in storage.values() if parse_numeric(v) > 0]
            if values:
                return max(values)
        return get_any_positive_party_consumption(party_key_value)

    def get_qty_per_bail_for_order(order, order_map_values, article_key):
        if order is None:
            return 0.0
        direct = parse_numeric(getattr(order, 'qty_bail', 0) or 0)
        if direct > 0:
            return direct
        direct_candidates = []
        for candidate in order_map_values:
            if candidate is None:
                continue
            candidate_value = parse_numeric(getattr(candidate, 'qty_bail', 0) or 0)
            if candidate_value > 0:
                direct_candidates.append(candidate_value)
        if direct_candidates:
            return max(direct_candidates)
        return 0.0

    def get_any_positive_party_consumption(party_key_value):
        storage = saved_party_consumption.get(party_key_value, {}) if isinstance(saved_party_consumption, dict) else {}
        values = [parse_numeric(v) for v in storage.values() if parse_numeric(v) > 0]
        return max(values) if values else 0.0

    normalized_party_consumption = {}
    for stored_party, value_map in saved_party_consumption.items():
        if not isinstance(value_map, dict):
            continue
        normalized_party = normalize_party_key(stored_party)
        if not normalized_party:
            continue
        normalized_party_consumption[normalized_party] = {
            make_article_key(article_key): parse_numeric(article_value)
            for article_key, article_value in value_map.items()
            if article_key is not None
        }
    saved_party_consumption = normalized_party_consumption

    def in_range(value):
        parsed = normalize_date(value)
        if not parsed or not start_date or not end_date:
            return False
        return start_date <= parsed.date() <= end_date

    party_key = normalize_party_key(party_name)

    if party_name and start_date and end_date and start_date <= end_date:
        party_orders = Order.query.filter(func.lower(Order.name) == party_name.lower()).all()
        party_order_ids = {order.job_no for order in party_orders if order.job_no}
        received_from_inventory = Inventory.query.filter(func.lower(Inventory.received_from) == party_name.lower()).all()
        party_order_ids.update(inventory.order_id for inventory in received_from_inventory if inventory.order_id)
        if party_order_ids:
            party_orders = Order.query.filter(Order.job_no.in_(party_order_ids)).all()
        order_map = {order.job_no: order for order in party_orders if order.job_no}
        inventories = Inventory.query.filter(Inventory.order_id.in_(order_map.keys())).all() if order_map else []
        inventory_ids = {inventory.id for inventory in inventories}
        inventory_by_id = {inventory.id: inventory for inventory in inventories}
        return_shipment_dates = {}
        return_shipment_challans = {}
        return_challans = ChallanRecord.query.filter(
            ChallanRecord.source_type.in_(('inventory_return', 'order'))
        ).all()
        for challan in return_challans:
            if challan.source_type == 'inventory_return' and challan.inventory_id:
                return_shipment_dates[challan.inventory_id] = challan.challan_date
                if challan.challan_no:
                    return_shipment_challans[challan.inventory_id] = challan.challan_no
            if challan.source_type != 'order' or not challan.combined_inventory_ids:
                continue
            try:
                combined_inventory_ids = json.loads(challan.combined_inventory_ids)
            except (TypeError, ValueError):
                combined_inventory_ids = []
            for inventory_id in combined_inventory_ids:
                return_shipment_dates[inventory_id] = challan.challan_date
                if challan.challan_no:
                    return_shipment_challans[inventory_id] = challan.challan_no
        articles = {}

        def article_bucket(order):
            key = (order.article or order.article_name or 'UNSPECIFIED').strip() or 'UNSPECIFIED'
            article_key = make_article_key(key)
            bucket_key = article_bucket_key(order)
            return articles.setdefault(bucket_key, {
                'article': key,
                'article_key': article_key,
                'article_bucket_key': bucket_key,
                'article_name': order.article_name or key,
                'article_style': order.style or '',
                'article_color': order.color or '',
                'consumption': parse_numeric(saved_party_consumption.get(party_key, {}).get(article_key, 0.0)),
                'opening_meter': 0.0, 'opening_bails': 0.0,
                'opening_bails_display': None,
                'received_meter': 0.0, 'received_bails': 0.0,
                'received_bails_display': None,
                'sent_meter': 0.0, 'sent_bails': 0.0, 'sent_aq_pcs': 0.0,
                'sent_challans': [],
                'sent_bails_display': None,
                'issued_meter': 0.0,
                'b_used_pcs': 0.0, 'b_used_meter': 0.0, 'b_used_bails': 0.0,
                'b_used_bails_display': None,
                'b_shipped_pcs': 0.0, 'b_shipped_meter': 0.0,
                'b_shipped_bails': 0.0, 'b_shipped_bails_display': None,
                'b_shipped_challans': [],
                'b_returned_meter': 0.0, 'b_returned_bails': 0.0,
                'b_returned_bails_display': None,
                'b_returned_challans': [],
            })

        for inventory in inventories:
            order = order_map.get(inventory.order_id)
            bucket = article_bucket(order)
            inventory_received_date = normalize_date(inventory.recv_date)
            b_returned_meter = (
                max(0.0, parse_numeric(inventory.b_returned_quantity))
                if inventory.b_returned_to_party else 0.0
            )
            received_meter = (
                parse_numeric(inventory.fabric_qty_a)
                + parse_numeric(inventory.fabric_qty_b)
            )
            received_bails = parse_numeric(inventory.receive_cut_pcs)
            if inventory_received_date and inventory_received_date.date() < start_date:
                bucket['opening_meter'] += received_meter
                bucket['opening_bails'] += received_bails
                return_challan_date = return_shipment_dates.get(inventory.id)
                return_date = normalize_date(
                    inventory.b_returned_shipped_date
                    or return_challan_date
                    or inventory.b_returned_date
                )
                if (
                    inventory.b_returned_to_party
                    and (
                        inventory.b_returned_shipped
                        or inventory.id in return_shipment_dates
                    )
                    and return_date
                    and return_date.date() < start_date
                ):
                    bucket['opening_meter'] -= b_returned_meter
            elif in_range(inventory.recv_date):
                bucket['received_meter'] += received_meter
                bucket['received_bails'] += received_bails

        inventory_rows = InventoryRow.query.filter(InventoryRow.inventory_id.in_(inventory_ids)).all() if inventory_ids else []
        for row in inventory_rows:
            inventory = inventory_by_id.get(row.inventory_id)
            order = order_map.get(inventory.order_id) if inventory else None
            if not order:
                continue
            bucket = article_bucket(order)
            amount = parse_numeric(row.fabric_issue)
            if in_range(row.date):
                bucket['issued_meter'] += amount

        def order_quality_meter_per_piece(order, quality):
            quality_split = get_cut_quality_split(order)
            cut_meter_by_no = {}
            total_meter = 0.0
            total_cut_pcs = 0.0
            for sheet in CuttingSheet.query.filter_by(order_id=order.job_no).all():
                sheet_meter = parse_numeric(sheet.total_meter) or parse_numeric(sheet.fabric_meter)
                sheet_pcs = (
                    parse_numeric(sheet.quantity)
                    or parse_numeric(sheet.summary_total_pcs)
                    or parse_numeric(sheet.total_pcs)
                )
                if sheet_meter > 0 and sheet_pcs > 0:
                    cut_meter_by_no[str(sheet.cut_no)] = sheet_meter / sheet_pcs
                    total_meter += sheet_meter
                    total_cut_pcs += sheet_pcs

            quality_pcs = sum(item[f'{quality}_pcs'] for item in quality_split)
            quality_meter = 0.0
            for item in quality_split:
                meter_per_piece = cut_meter_by_no.get(str(item.get('cut_no')), 0.0)
                if meter_per_piece <= 0 and total_cut_pcs > 0:
                    meter_per_piece = total_meter / total_cut_pcs
                quality_meter += item[f'{quality}_pcs'] * meter_per_piece
            if quality_pcs > 0:
                return quality_meter / quality_pcs
            return total_meter / total_cut_pcs if total_cut_pcs > 0 else 0.0

        for order in party_orders:
            bucket = article_bucket(order)
            meter_per_aq_piece = order_quality_meter_per_piece(order, 'aq')
            meter_per_bq_piece = order_quality_meter_per_piece(order, 'bq')
            article_consumption = get_saved_consumption_for_order(
                party_key, order, bucket.get('article_key')
            )
            if article_consumption > 0 and parse_numeric(order.pcs_poly) > 0 and parse_numeric(order.qty_bail) > 0:
                meter_per_bq_piece = article_consumption / 12
                meter_per_aq_piece = article_consumption / 12
            pcs_per_bail = parse_numeric(order.pcs_poly) * parse_numeric(order.qty_bail)
            shipments = ShipmentRecord.query.filter_by(order_id=order.id).all()
            if shipments:
                shipment_entries = [
                    (
                        parse_numeric(shipment.shipped_aq_pcs),
                        parse_numeric(shipment.shipped_bq_pcs),
                        shipment.shipped_at,
                        shipment.id,
                    )
                    for shipment in shipments
                ]
            else:
                shipping = get_order_shipping_snapshot(order)
                shipment_entries = [(
                    shipping['shipped_aq_pcs'],
                    shipping['shipped_bq_pcs'],
                    order.shipped_at or order.delivered_at or order.date,
                    None,
                )]

            def get_shipment_challan(shipment_id):
                if not shipment_id:
                    return None
                challan = ChallanRecord.query.filter_by(
                    shipment_id=shipment_id,
                    source_type='order',
                ).first()
                if challan is None:
                    for grouped_challan in ChallanRecord.query.filter_by(source_type='order').all():
                        try:
                            grouped_shipment_ids = json.loads(grouped_challan.combined_shipment_ids or '[]')
                        except (TypeError, ValueError):
                            grouped_shipment_ids = []
                        if shipment_id in grouped_shipment_ids:
                            challan = grouped_challan
                            break
                return challan

            for aq_pcs, bq_pcs, shipment_date, shipment_id in shipment_entries:
                if not in_range(shipment_date):
                    continue
                aq_shipment_meter = aq_pcs * meter_per_aq_piece
                bq_shipment_meter = bq_pcs * meter_per_bq_piece
                if article_consumption > 0 and parse_numeric(order.pcs_poly) > 0 and parse_numeric(order.qty_bail) > 0:
                    shipment_meter = round((aq_pcs + bq_pcs) * article_consumption / 12, 2)
                    aq_shipment_meter = round(aq_pcs * article_consumption / 12, 2)
                    bq_shipment_meter = shipment_meter - aq_shipment_meter
                if aq_pcs > 0:
                    bucket['sent_aq_pcs'] += aq_pcs
                    bucket['sent_meter'] += aq_shipment_meter
                    if pcs_per_bail > 0:
                        bucket['sent_bails'] += aq_pcs / pcs_per_bail
                    else:
                        bucket['sent_bails_display'] = 'N/A'
                    challan = get_shipment_challan(shipment_id)
                    if challan and challan.challan_no and challan.challan_no not in bucket['sent_challans']:
                            bucket['sent_challans'].append(challan.challan_no)
                if bq_pcs > 0:
                    bucket['b_shipped_pcs'] += bq_pcs
                    bucket['b_shipped_meter'] += bq_shipment_meter
                    if pcs_per_bail > 0:
                        bucket['b_shipped_bails'] += bq_pcs / pcs_per_bail
                    else:
                        bucket['b_shipped_bails_display'] = 'N/A'
                    challan = get_shipment_challan(shipment_id)
                    if challan and challan.challan_no and challan.challan_no not in bucket['b_shipped_challans']:
                        bucket['b_shipped_challans'].append(challan.challan_no)

        for inventory in inventories:
            if (
                not inventory.b_returned_to_party
                or (
                    not inventory.b_returned_shipped
                    and inventory.id not in return_shipment_dates
                )
            ):
                continue
            b_returned_meter = max(0.0, parse_numeric(inventory.b_returned_quantity))
            return_date = (
                inventory.b_returned_shipped_date
                or return_shipment_dates.get(inventory.id)
                or inventory.b_returned_date
            )
            if b_returned_meter <= 0 or not in_range(return_date):
                continue

            order = order_map.get(inventory.order_id) if inventory else None
            if not order:
                continue

            bucket = article_bucket(order)
            bucket['b_returned_meter'] += b_returned_meter
            return_challan_no = return_shipment_challans.get(inventory.id)
            if return_challan_no and return_challan_no not in bucket['b_returned_challans']:
                bucket['b_returned_challans'].append(return_challan_no)

            article_key = bucket.get('article_key') or make_article_key((order.article or order.article_name or 'UNSPECIFIED'))
            consumption = get_saved_consumption_for_order(party_key, order, article_key)
            qty_per_bail = get_qty_per_bail_for_order(order, order_map.values(), article_key)

            b_returned_bails = 0.0
            if consumption > 0 and qty_per_bail > 0:
                req_per_dozen = b_returned_meter / consumption
                b_returned_bails = round((req_per_dozen / qty_per_bail), 2)
                bucket['b_returned_bails_display'] = None
            else:
                bucket['b_returned_bails_display'] = 'N/A'
            bucket['b_returned_bails'] += b_returned_bails

        for inventory in inventories:
            order = order_map.get(inventory.order_id)
            if not order:
                continue
            bucket = article_bucket(order)
            b_usage = calculate_inventory_b_usage_for_period(inventory, start_date, end_date, inventory.order_id)
            b_used_meter = b_usage['meter']
            bucket['b_used_meter'] += b_used_meter
            bucket['b_used_pcs'] += b_usage['pcs']

            article_key = bucket.get('article_key') or make_article_key((order.article or order.article_name or 'UNSPECIFIED'))
            consumption = get_saved_consumption_for_order(party_key, order, article_key)
            qty_per_bail = get_qty_per_bail_for_order(order, order_map.values(), article_key)
            b_used_bails = 0.0
            if b_used_meter == 0:
                bucket['b_used_bails_display'] = None
            elif b_used_meter > 0 and consumption > 0 and qty_per_bail > 0:
                req_per_dozen = b_used_meter / consumption
                b_used_bails = round((req_per_dozen / qty_per_bail), 2)
                bucket['b_used_bails_display'] = None
            else:
                bucket['b_used_bails_display'] = 'N/A'
            bucket['b_used_bails'] += b_used_bails

        for bucket in articles.values():
            same_article_orders = [
                candidate for candidate in order_map.values()
                if article_bucket_key(candidate) == bucket.get('article_bucket_key')
            ]
            chosen_order = same_article_orders[0] if same_article_orders else None
            consumption = get_saved_consumption_for_order(party_key, chosen_order, bucket.get('article_key'))
            qty_per_bail = get_qty_per_bail_for_order(chosen_order, same_article_orders, bucket.get('article_key'))

            if bucket['opening_meter'] == 0:
                bucket['opening_bails'] = 0.0
                bucket['opening_bails_display'] = None
            elif bucket['opening_meter'] > 0 and consumption > 0 and qty_per_bail > 0:
                req_per_dozen = bucket['opening_meter'] / consumption
                bucket['opening_bails'] = round((req_per_dozen / qty_per_bail), 2)
                bucket['opening_bails_display'] = None
            else:
                bucket['opening_bails_display'] = 'N/A'
                bucket['opening_bails'] = 0.0

            if bucket['received_meter'] == 0:
                bucket['received_bails'] = 0.0
                bucket['received_bails_display'] = None
            elif bucket['received_meter'] > 0 and consumption > 0 and qty_per_bail > 0:
                req_per_dozen = bucket['received_meter'] / consumption
                bucket['received_bails'] = round((req_per_dozen / qty_per_bail), 2)
                bucket['received_bails_display'] = None
            else:
                bucket['received_bails_display'] = 'N/A'
                bucket['received_bails'] = 0.0

            if bucket['sent_aq_pcs'] == 0:
                bucket['sent_bails'] = 0.0
                bucket['sent_bails_display'] = None
            elif bucket['sent_bails_display'] != 'N/A':
                bucket['sent_bails_display'] = None

            if bucket['b_shipped_pcs'] > 0 and bucket['b_shipped_bails_display'] != 'N/A':
                bucket['b_shipped_bails_display'] = None

            bucket['balance_meter'] = (
                bucket['opening_meter']
                + bucket['received_meter']
                - bucket['sent_meter']
                - bucket['b_shipped_meter']
                - bucket['b_returned_meter']
            )

            if bucket['balance_meter'] == 0:
                bucket['balance_bails'] = 0.0
                bucket['balance_bails_display'] = None
            elif consumption > 0 and qty_per_bail > 0:
                req_per_dozen = bucket['balance_meter'] / consumption
                bucket['balance_bails'] = round((req_per_dozen / qty_per_bail), 2)
                bucket['balance_bails_display'] = None
            else:
                bucket['balance_bails_display'] = 'N/A'
                bucket['balance_bails'] = 0.0
        rows = sorted(articles.values(), key=lambda row: row['article'])

    return render_template(
        'fabric_position_summary.html', rows=rows, party_name=party_name,
        start_date=start_value, end_date=end_value,
        prepared_by=session.get('name') or session.get('user') or 'System',
    )


@app.route('/stock-portal/article-fabric-and-shipment-summary')
def article_fabric_and_shipment_summary():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    party_name = (request.args.get('party_name') or '').strip()
    start_value = (request.args.get('start_date') or '').strip()
    end_value = (request.args.get('end_date') or '').strip()
    start_date = normalize_date(start_value).date() if normalize_date(start_value) else None
    end_date = normalize_date(end_value).date() if normalize_date(end_value) else None
    date_range_active = bool(start_date and end_date and start_date <= end_date)
    consumption = parse_numeric(request.args.get('consumption') or 0)
    storage_key = 'party-article-consumption'
    saved_party_consumption = load_party_article_consumption()
    if not isinstance(saved_party_consumption, dict):
        saved_party_consumption = {}
    normalized_party_consumption = {}
    for stored_party, value_map in saved_party_consumption.items():
        if not isinstance(value_map, dict):
            continue
        normalized_party = normalize_party_key(stored_party)
        if not normalized_party:
            continue
        normalized_party_consumption[normalized_party] = {
            make_article_key(article_key): parse_numeric(article_value)
            for article_key, article_value in value_map.items()
            if article_key is not None
        }
    saved_party_consumption = normalized_party_consumption

    consumption_by_article = {}
    party_key = normalize_party_key(party_name)
    for key, value in request.args.items():
        if key.startswith('article_consumption_'):
            article_key = make_article_key(key[len('article_consumption_'):].strip())
            if article_key:
                parsed_value = parse_numeric(value)
                consumption_by_article[article_key] = parsed_value
                if parsed_value > 0:
                    saved_party_consumption.setdefault(party_key, {})[article_key] = parsed_value
                    save_party_article_consumption(party_name, article_key, parsed_value)
                elif article_key in saved_party_consumption.get(party_key, {}):
                    saved_party_consumption.setdefault(party_key, {}).pop(article_key, None)
                    save_party_article_consumption(party_name, article_key, 0)
                if party_key and not saved_party_consumption.get(party_key):
                    saved_party_consumption.pop(party_key, None)
    if party_name:
        session[storage_key] = saved_party_consumption

    if party_key and isinstance(saved_party_consumption.get(party_key), dict):
        for article_key, value in saved_party_consumption[party_key].items():
            consumption_by_article.setdefault(article_key, value)

    party_names = sorted({
        (party_name_value or '').strip()
        for (party_name_value,) in db.session.query(Article.party_name)
        .filter(Article.party_name.isnot(None), Article.party_name != '')
        .distinct()
        .all()
        if party_name_value and party_name_value.strip()
    })

    rows = []
    if party_name:
        party_orders = Order.query.filter(func.lower(Order.name) == party_name.lower()).all()
        party_order_ids = {order.job_no for order in party_orders if order.job_no}

        received_from_inventory = Inventory.query.filter(func.lower(Inventory.received_from) == party_name.lower()).all()
        party_order_ids.update(inventory.order_id for inventory in received_from_inventory if inventory.order_id)

        if party_order_ids:
            party_orders = Order.query.filter(Order.job_no.in_(party_order_ids)).all()

        order_map = {order.job_no: order for order in party_orders if order.job_no}
        inventory_records = Inventory.query.filter(Inventory.order_id.in_(list(party_order_ids))).all() if party_order_ids else []
        article_buckets = {}

        def order_conversion_to_meter(order_obj):
            if not order_obj:
                return {'meter_per_pcs': 0.0, 'total_meter': 0.0, 'completed_pcs': 0.0, 'a_meter_per_pcs': 0.0, 'b_meter_per_pcs': 0.0}

            quality_split = get_cut_quality_split(order_obj)
            cut_pcs_by_no = {}
            total_meter = 0.0
            total_completed_pcs = 0.0
            for sheet in CuttingSheet.query.filter_by(order_id=order_obj.job_no).all():
                sheet_meter = parse_numeric(sheet.total_meter) or parse_numeric(sheet.fabric_meter) or 0.0
                sheet_pcs = (
                    parse_numeric(sheet.quantity)
                    or parse_numeric(sheet.summary_total_pcs)
                    or parse_numeric(sheet.total_pcs)
                    or 0.0
                )
                if sheet_meter > 0 and sheet_pcs > 0:
                    total_meter += sheet_meter
                    total_completed_pcs += sheet_pcs
                    cut_pcs_by_no[str(sheet.cut_no)] = sheet_meter / sheet_pcs

            total_a_pcs = sum(item['aq_pcs'] for item in quality_split)
            total_b_pcs = sum(item['bq_pcs'] for item in quality_split)
            total_a_meter = 0.0
            total_b_meter = 0.0
            for item in quality_split:
                meter_per_cut_pcs = cut_pcs_by_no.get(str(item.get('cut_no')), 0.0)
                if meter_per_cut_pcs <= 0 and total_completed_pcs > 0 and total_meter > 0:
                    meter_per_cut_pcs = total_meter / total_completed_pcs
                total_a_meter += item.get('aq_pcs', 0.0) * meter_per_cut_pcs
                total_b_meter += item.get('bq_pcs', 0.0) * meter_per_cut_pcs

            meter_per_pcs = (total_meter / total_completed_pcs) if total_meter > 0 and total_completed_pcs > 0 else 0.0
            a_meter_per_pcs = (total_a_meter / total_a_pcs) if total_a_pcs > 0 else meter_per_pcs
            b_meter_per_pcs = (total_b_meter / total_b_pcs) if total_b_pcs > 0 else meter_per_pcs

            return {
                'meter_per_pcs': meter_per_pcs,
                'total_meter': total_meter,
                'completed_pcs': total_completed_pcs,
                'a_meter_per_pcs': a_meter_per_pcs,
                'b_meter_per_pcs': b_meter_per_pcs,
            }

        def article_bucket(article_label):
            key = (article_label or 'UNSPECIFIED').strip() or 'UNSPECIFIED'
            article_key = make_article_key(key)
            if article_key not in article_buckets:
                article_buckets[article_key] = {
                    'article': key,
                    'article_name': key,
                    'article_style': '',
                    'article_color': '',
                    'article_key': article_key,
                    'article_consumption': consumption_by_article.get(article_key, saved_party_consumption.get(party_key, {}).get(article_key, consumption or 0.0)),
                    'opening_meter': 0.0,
                    'opening_totals': {
                        'fabric_a': 0.0,
                        'fabric_b': 0.0,
                        'fabric_c': 0.0,
                    },
                    'received_meter': 0.0,
                    'received_bails': 0.0,
                    'shipment_meter': 0.0,
                    'shipment_bails': 0.0,
                    'shipment_rows': [],
                    'req_per_dozen': 0.0,
                    'req_bail': 0.0,
                    'qty_per_bail': 0.0,
                    'order_count': 0,
                    'records': {},
                    'totals': {
                        'fabric_a': 0.0,
                        'fabric_b': 0.0,
                        'fabric_c': 0.0,
                        'total': 0.0,
                        'req_per_dozen': 0.0,
                        'req_bail': 0.0,
                    },
                }
            article_buckets[article_key]['article_consumption'] = consumption_by_article.get(
                article_key,
                saved_party_consumption.get(party_key, {}).get(article_key, article_buckets[article_key].get('article_consumption') or consumption or 0.0),
            )
            return article_buckets[article_key]

        for order in party_orders:
            article_label = (order.article_name or order.article or 'UNSPECIFIED').strip() or 'UNSPECIFIED'
            bucket = article_bucket(article_label)
            bucket['article_name'] = order.article_name or article_label
            bucket['article_style'] = order.style or bucket.get('article_style') or ''
            bucket['article_color'] = order.color or bucket.get('article_color') or ''
            bucket['order_count'] += 1
            qty_per_bail = parse_numeric(order.qty_bail)
            if qty_per_bail > 0:
                bucket['qty_per_bail'] += qty_per_bail

        for order in party_orders:
            article_label = (order.article_name or order.article or 'UNSPECIFIED').strip() or 'UNSPECIFIED'
            bucket = article_bucket(article_label)
            bucket['article_name'] = order.article_name or article_label
            bucket['article_style'] = order.style or bucket.get('article_style') or ''
            bucket['article_color'] = order.color or bucket.get('article_color') or ''
            conversion = order_conversion_to_meter(order)

            cumulative_fab_use = 0.0
            for shipment in ShipmentRecord.query.filter_by(order_id=order.id).order_by(ShipmentRecord.id.asc()).all():
                shipment_date = normalize_date(shipment.shipped_at)
                if date_range_active and (
                    not shipment_date
                    or not start_date <= shipment_date.date() <= end_date
                ):
                    continue
                shipped_aq_pcs = parse_numeric(shipment.shipped_aq_pcs)
                shipped_bq_pcs = parse_numeric(shipment.shipped_bq_pcs)
                shipment_pcs = shipped_aq_pcs + shipped_bq_pcs
                if shipment_pcs <= 0:
                    shipment_pcs = parse_numeric(getattr(shipment, 'shipped_pcs', 0))
                stored_shipped_bails = parse_numeric(getattr(shipment, 'shipped_bails', 0))
                if stored_shipped_bails <= 0:
                    stored_shipped_bails = parse_numeric(getattr(shipment, 'shipped_aq_bails', 0)) + parse_numeric(getattr(shipment, 'shipped_bq_bails', 0))
                if shipment_pcs <= 0 and stored_shipped_bails <= 0:
                    continue

                shipment_challan = ChallanRecord.query.filter_by(shipment_id=shipment.id, source_type='order').first()
                if shipment_challan is None:
                    for grouped_challan in ChallanRecord.query.filter_by(source_type='order').all():
                        try:
                            grouped_shipment_ids = json.loads(grouped_challan.combined_shipment_ids or '[]')
                        except (TypeError, ValueError):
                            grouped_shipment_ids = []
                        if shipment.id in grouped_shipment_ids:
                            shipment_challan = grouped_challan
                            break
                shipment_challan_no = shipment_challan.challan_no if shipment_challan else (shipment.job_no or order.job_no or '-')

                article_consumption = bucket.get('article_consumption') or 0.0
                order_qty_per_bail = parse_numeric(order.qty_bail)
                pcs_per_packet = parse_numeric(order.pcs_poly)
                pcs_per_bail = pcs_per_packet * order_qty_per_bail
                shipment_bails = (
                    shipment_pcs / pcs_per_bail
                    if shipment_pcs > 0 and pcs_per_bail > 0
                    else stored_shipped_bails
                )
                if article_consumption > 0 and order_qty_per_bail > 0:
                    shipment_meter = (
                        shipment_bails
                        * article_consumption
                        * order_qty_per_bail
                        * pcs_per_packet
                        / 12
                    )
                else:
                    shipment_meter = (
                        shipped_aq_pcs * (conversion['a_meter_per_pcs'] or conversion['meter_per_pcs'])
                        + shipped_bq_pcs * (conversion['b_meter_per_pcs'] or conversion['meter_per_pcs'])
                    )
                shipment_meter = round(shipment_meter, 2)
                shipment_bails = round(shipment_bails, 2)
                cumulative_fab_use += shipment_meter
                balance_bails = 0.0
                if article_consumption > 0:
                    balance_bails = max(0.0, (bucket['opening_meter'] - cumulative_fab_use) / article_consumption)
                if shipped_aq_pcs > 0.000001 and shipped_bq_pcs > 0.000001:
                    shipment_type = 'A/Q + B/Q'
                elif shipped_aq_pcs > 0.000001:
                    shipment_type = 'A/Q'
                elif shipped_bq_pcs > 0.000001:
                    shipment_type = 'B/Q'
                else:
                    shipment_type = 'C/P'
                row = {
                    'date': shipment.shipped_at or order.date or 'N/A',
                    'challan_no': shipment_challan_no,
                    'shipment_type': shipment_type,
                    'shipment_meter': shipment_meter,
                    'shipment_bails': shipment_bails,
                    'balance_bails': round(balance_bails, 2),
                    'fab_use': shipment_meter,
                    'fab_bal': 0.0,
                }
                bucket['shipment_rows'].append(row)
                bucket['shipment_meter'] += shipment_meter
                bucket['shipment_bails'] += shipment_bails

        for inventory in inventory_records:
            if any(str(shipment.job_no or '') == str(inventory.challan_no or '') for order in party_orders for shipment in ShipmentRecord.query.filter_by(order_id=order.id).all()):
                continue

            order = order_map.get(inventory.order_id)
            article_label = (order.article_name or order.article or inventory.item_name or 'UNSPECIFIED').strip() if order else (inventory.item_name or 'UNSPECIFIED')
            bucket = article_bucket(article_label)
            bucket['article_name'] = (order.article_name or order.article or bucket['article_name']).strip() if order else bucket['article_name']

            fabric_a = parse_numeric(inventory.fabric_qty_a)
            fabric_b = parse_numeric(inventory.fabric_qty_b)
            fabric_c = parse_numeric(inventory.total) - fabric_a - fabric_b if parse_numeric(inventory.total) > 0 else 0.0
            total_meter = parse_numeric(inventory.total) if parse_numeric(inventory.total) > 0 else fabric_a + fabric_b
            inventory_received_date = normalize_date(inventory.recv_date)
            before_start_date = bool(
                date_range_active
                and inventory_received_date
                and inventory_received_date.date() < start_date
            )
            in_selected_range = bool(
                not date_range_active
                or (
                    inventory_received_date
                    and start_date <= inventory_received_date.date() <= end_date
                )
            )

            bucket['received_meter'] += total_meter if in_selected_range else 0.0
            bucket['received_bails'] += parse_numeric(inventory.receive_cut_pcs) if in_selected_range else 0.0
            if before_start_date:
                bucket['opening_meter'] += total_meter
                bucket['opening_totals']['fabric_a'] += fabric_a
                bucket['opening_totals']['fabric_b'] += fabric_b
                bucket['opening_totals']['fabric_c'] += fabric_c

            if in_selected_range:
                date_key = (inventory.recv_date or '').strip() or 'N/A'
                entry_key = f"{date_key}|{inventory.challan_no or inventory.serial_no or inventory.id}"
                date_entry = bucket['records'].setdefault(entry_key, {
                    'date': date_key,
                    'challan_no': inventory.challan_no or '-',
                    'width': inventory.width or '-',
                    'fabric_a': 0.0,
                    'fabric_b': 0.0,
                    'fabric_c': 0.0,
                    'total': 0.0,
                    'req_per_dozen': 0.0,
                    'req_bail': 0.0,
                })
                date_entry['fabric_a'] += fabric_a
                date_entry['fabric_b'] += fabric_b
                date_entry['fabric_c'] += fabric_c
                date_entry['total'] += total_meter

            shipment_meter = 0.0
            shipment_bails = 0.0
            fab_use = 0.0
            for row in inventory.rows:
                shipment_meter += parse_numeric(row.fabric_issue)
                shipment_bails += parse_numeric(row.cutting_pcs)
                fab_use += parse_numeric(row.fabric_use)
            bucket['shipment_meter'] += shipment_meter
            bucket['shipment_bails'] += shipment_bails

            returned_meter = max(0.0, parse_numeric(getattr(inventory, 'b_returned_quantity', 0)))
            if getattr(inventory, 'b_returned_to_party', False) and getattr(inventory, 'b_returned_shipped', False) and returned_meter > 0:
                article_consumption = bucket.get('article_consumption') or 0.0
                return_order = order_map.get(inventory.order_id)
                qty_per_bail = parse_numeric(getattr(return_order, 'qty_bail', 0)) if return_order else 0.0
                if qty_per_bail <= 0 and bucket.get('order_count', 0) > 0:
                    qty_per_bail = (bucket.get('qty_per_bail') or 0.0) / bucket['order_count']
                returned_bails = (
                    (returned_meter / article_consumption) / qty_per_bail
                    if article_consumption > 0 and qty_per_bail > 0
                    else 0.0
                )
                returned_meter = round(returned_meter, 2)
                returned_bails = round(returned_bails, 2)
                returned_date = (getattr(inventory, 'b_returned_date', '') or inventory.recv_date or 'N/A').strip()
                return_challan = ChallanRecord.query.filter_by(inventory_id=inventory.id, source_type='inventory_return').first()
                if return_challan is None:
                    for challan in ChallanRecord.query.filter_by(source_type='order').all():
                        try:
                            combined_inventory_ids = json.loads(challan.combined_inventory_ids or '[]')
                        except (TypeError, ValueError):
                            combined_inventory_ids = []
                        if inventory.id in combined_inventory_ids:
                            return_challan = challan
                            break
                returned_date = (
                    getattr(inventory, 'b_returned_shipped_date', '')
                    or (return_challan.challan_date if return_challan else '')
                    or getattr(inventory, 'b_returned_date', '')
                    or inventory.recv_date
                    or 'N/A'
                ).strip()
                parsed_returned_date = normalize_date(returned_date)
                if date_range_active and (
                    not parsed_returned_date
                    or not start_date <= parsed_returned_date.date() <= end_date
                ):
                    continue
                return_challan_no = return_challan.challan_no if return_challan else f"RETURNED-{inventory.serial_no or inventory.id}"
                bucket['shipment_rows'].append({
                    'date': returned_date,
                    'challan_no': return_challan_no,
                    'shipment_type': 'F/R',
                    'shipment_meter': returned_meter,
                    'shipment_bails': returned_bails,
                    'balance_bails': 0.0,
                    'fab_use': returned_meter,
                    'fab_bal': 0.0,
                })
                bucket['shipment_meter'] += returned_meter
                bucket['shipment_bails'] += returned_bails

        for bucket in article_buckets.values():
            if bucket['qty_per_bail'] > 0:
                bucket['qty_per_bail'] = bucket['qty_per_bail'] / max(1, bucket['order_count'])

            article_consumption = bucket.get('article_consumption') or 0.0
            bucket['opening_meter'] = round(max(0.0, bucket.get('opening_meter', 0.0)), 1)
            for field in ('fabric_a', 'fabric_b', 'fabric_c'):
                bucket['opening_totals'][field] = round(bucket['opening_totals'][field], 1)

            for entry in bucket['records'].values():
                for field in ('fabric_a', 'fabric_b', 'fabric_c', 'total'):
                    entry[field] = round(entry[field], 1)
                if article_consumption > 0:
                    entry['req_per_dozen'] = round(entry['total'] / article_consumption, 2)
                    entry['req_bail'] = round(
                        entry['req_per_dozen'] / bucket['qty_per_bail'], 2
                    ) if bucket['qty_per_bail'] > 0 else 0.0
                bucket['totals']['fabric_a'] += entry['fabric_a']
                bucket['totals']['fabric_b'] += entry['fabric_b']
                bucket['totals']['fabric_c'] += entry['fabric_c']
                bucket['totals']['total'] += entry['total']
                bucket['totals']['req_per_dozen'] += entry['req_per_dozen']
                bucket['totals']['req_bail'] += entry['req_bail']

            opening_req_per_dozen = 0.0
            opening_req_bails = 0.0
            if article_consumption > 0:
                opening_req_per_dozen = round(bucket['opening_meter'] / article_consumption, 2)
                if bucket['qty_per_bail'] > 0:
                    opening_req_bails = round(
                        (bucket['opening_meter'] / article_consumption) / bucket['qty_per_bail'], 2
                    )

            for field in ('fabric_a', 'fabric_b', 'fabric_c'):
                bucket['totals'][field] += bucket['opening_totals'][field]
            bucket['totals']['req_per_dozen'] += opening_req_per_dozen
            bucket['totals']['req_bail'] += opening_req_bails
            opening_fab_use = round(
                bucket['opening_meter'] + bucket['totals'].get('total', 0.0), 2
            )
            opening_bal_bails = bucket['totals']['req_bail']

            bucket['totals']['total'] += bucket['opening_meter']

            bucket['shipment_rows'].sort(
                key=lambda item: normalize_date(item.get('date')) or datetime.max
            )

            opening_row = {
                'date': 'O/B',
                'challan_no': 'O/B',
                'shipment_type': '',
                'shipment_meter': 0.0,
                'shipment_bails': 0.0,
                'balance_bails': opening_bal_bails,
                'fab_use': 0.0,
                'fab_bal': opening_fab_use,
            }
            if bucket['shipment_rows'] and bucket['shipment_rows'][0].get('date') == 'O/B':
                bucket['shipment_rows'][0] = opening_row
            else:
                bucket['shipment_rows'].insert(0, opening_row)

            running_fab_use = 0.0
            running_ship_bails = 0.0
            for shipment_row in bucket['shipment_rows']:
                if shipment_row.get('date') == 'O/B':
                    shipment_row['balance_bails'] = opening_bal_bails
                    shipment_row['fab_use'] = opening_fab_use
                    shipment_row['fab_bal'] = opening_fab_use
                    shipment_row['shipment_bails'] = 0.0
                    shipment_row['shipment_meter'] = 0.0
                    continue

                current_fab_use = parse_numeric(shipment_row.get('fab_use'))
                running_fab_use += current_fab_use
                running_ship_bails += parse_numeric(shipment_row.get('shipment_bails'))
                shipment_row['fab_bal'] = round(max(0.0, opening_fab_use - running_fab_use), 2)
                if article_consumption > 0:
                    shipment_row['balance_bails'] = round(
                        max(0.0, opening_bal_bails - running_ship_bails), 2
                    )
                else:
                    shipment_row['balance_bails'] = 0.0

            rows.append(bucket)

        rows.sort(key=lambda item: item['article_name'])

    return render_template(
        'article_fabric_and_shipment_summary.html',
        party_names=party_names,
        party_name=party_name,
        consumption=consumption,
        rows=rows,
        prepared_by=session.get('name') or session.get('user') or 'System',
    )


LOCAL_ACCESSORY_PO_ORDER_ID = 'LOCAL-STOCK'


@app.route('/stock-portal/accessories', defaults={'portal_page': 'home'}, methods=['GET', 'POST'])
@app.route('/stock-portal/accessories/<portal_page>', methods=['GET', 'POST'])
def accessories_portal(portal_page='home'):
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    if portal_page not in {'home', 'purchase-orders', 'unallocated-stock', 'issuance-store-finder', 'issued-returned-items'}:
        abort(404)

    def redirect_to_portal(page=None, **query):
        destination = page or portal_page
        if destination == 'home':
            return redirect(url_for('accessories_portal', **query))
        return redirect(url_for('accessories_portal', portal_page=destination, **query))

    if request.method == 'POST':
        action = request.form.get('action')
        if action == 'record_party_accessory':
            if is_read_only_profile():
                return reject_read_only_edit('This profile has read-only access to accessory stock.')

            sent_date = (request.form.get('party_accessory_date') or '').strip()
            order_id = (request.form.get('party_accessory_order') or '').strip()
            item_name = (request.form.get('party_accessory_item') or '').strip()
            quantity = parse_numeric(request.form.get('party_accessory_quantity'))
            unit = (request.form.get('party_accessory_unit') or '').strip()
            issue_unit = (request.form.get('party_accessory_issue_unit') or unit).strip().upper()
            entered_factor = parse_numeric(request.form.get('party_accessory_issue_factor'))
            factor_mode = (request.form.get('party_accessory_issue_factor_mode') or 'STOCK_PER_ISSUE').strip().upper()
            try:
                datetime.strptime(sent_date, '%Y-%m-%d')
            except ValueError:
                flash('Choose a valid date for the party-supplied accessory.', 'danger')
                return redirect_to_portal('purchase-orders')

            order = Order.query.filter_by(job_no=order_id).first()
            if not order or not item_name or quantity <= 0 or not unit:
                flash('Choose an order and enter an item, quantity, and unit.', 'danger')
                return redirect_to_portal('purchase-orders')
            if issue_unit.casefold() == unit.casefold():
                issue_factor = 1.0
            elif entered_factor <= 0:
                flash('Enter the unit conversion needed for issuing this party-supplied accessory.', 'danger')
                return redirect_to_portal('purchase-orders')
            elif factor_mode == 'ISSUE_PER_STOCK':
                issue_factor = 1.0 / entered_factor
            else:
                issue_factor = entered_factor

            party_entry = PartySuppliedAccessory(
                sent_date=sent_date,
                order_id=order.job_no,
                party_name=(order.name or '').strip(),
                article_name=(order.article_name or order.article or '').strip(),
                item=item_name,
                size=(request.form.get('party_accessory_size') or '').strip(),
                quality=(request.form.get('party_accessory_quality') or '').strip(),
                quantity=quantity,
                unit=unit,
                note=(request.form.get('party_accessory_note') or '').strip(),
                recorded_by=(session.get('name') or session.get('user') or '').strip(),
            )
            db.session.add(party_entry)
            db.session.flush()
            roll_length_m = length_to_meters(issue_factor, unit) if is_roll_unit(issue_unit) else 0.0
            db.session.add(SavedRequirement(
                serial_no=f'PARTY-SUPPLIED-{party_entry.id}',
                order_id=LOCAL_ACCESSORY_PO_ORDER_ID,
                item=item_name,
                qty=str(quantity),
                size=party_entry.size,
                unit=unit,
                roll_length_m=roll_length_m,
                issue_unit=issue_unit,
                issue_unit_factor=issue_factor,
                quality=party_entry.quality,
                supplier=order.name or '',
                requested_by=party_entry.recorded_by,
                date=sent_date,
                for_field=f'PARTY SUPPLIED · {order.job_no}',
                accessory_status='RECEIVED',
                received_qty=str(quantity),
                issued_qty='0',
                used_qty=str(quantity),
                received_at=sent_date,
            ))
            db.session.commit()
            flash('Party-supplied accessory recorded.', 'success')
            return redirect_to_portal('purchase-orders')

        if action == 'create_local_po':
            if is_read_only_profile():
                return reject_read_only_edit('This profile has read-only access to accessory stock.')

            supplier = (request.form.get('local_supplier') or '').strip()
            requested_by = (request.form.get('local_requested_by') or '').strip()
            po_date = (request.form.get('local_date') or '').strip()
            priority = (request.form.get('local_priority') or 'Normal').strip()
            if not supplier or not requested_by or not po_date:
                flash('Supplier, requested by, and date are required for a Local PO.', 'danger')
                return redirect_to_portal('purchase-orders')

            try:
                datetime.strptime(po_date, '%Y-%m-%d')
            except ValueError:
                flash('Enter a valid Local PO date.', 'danger')
                return redirect_to_portal('purchase-orders')

            local_items = []
            for row_number in range(1, 7):
                item_name = (request.form.get(f'local_item_{row_number}') or '').strip()
                qty_value = (request.form.get(f'local_qty_{row_number}') or '').strip()
                size = (request.form.get(f'local_size_{row_number}') or '').strip()
                quality = (request.form.get(f'local_quality_{row_number}') or '').strip()
                unit = (request.form.get(f'local_unit_{row_number}') or 'PCS').strip() or 'PCS'
                rate_value = (request.form.get(f'local_rate_{row_number}') or '').strip()
                if not any((item_name, qty_value, size, quality, rate_value)):
                    continue
                qty = parse_numeric(qty_value)
                rate = parse_numeric(rate_value)
                roll_length_m = 0.0
                vendor = Vendor.query.filter(func.lower(func.trim(Vendor.name)) == supplier.casefold()).first()
                vendor_item = next((
                    candidate for candidate in (vendor.items if vendor else [])
                    if (candidate.item_name or '').strip().casefold() == item_name.casefold()
                ), None)
                if rate <= 0 and vendor_item:
                    vendor_unit = (vendor_item.unit or '').strip()
                    if vendor_unit.casefold() == unit.casefold():
                        if is_roll_unit(vendor_unit) or is_package_unit(vendor_unit):
                            vendor_pack_qty = parse_numeric(vendor_item.pack_qty)
                            vendor_rate = parse_numeric(vendor_item.rate)
                            rate = parse_numeric(vendor_item.pack_price) or (
                                vendor_rate * vendor_pack_qty if vendor_pack_qty > 0 else vendor_rate
                            )
                        else:
                            rate = parse_numeric(vendor_item.rate) or calculate_vendor_unit_rate(
                                vendor_item.pack_qty, vendor_item.pack_price
                            )
                    elif is_roll_unit(vendor_unit) and length_to_meters(1, unit) > 0:
                        roll_meters = length_to_meters(vendor_item.pack_qty, 'METER')
                        if roll_meters > 0:
                            rate = (parse_numeric(vendor_item.pack_price) or parse_numeric(vendor_item.rate)) / roll_meters
                    else:
                        unit_factor = unit_conversion_factor(vendor_unit, unit)
                        if unit_factor is not None and unit_factor > 0:
                            rate = parse_numeric(vendor_item.rate) * unit_factor
                if is_roll_unit(unit):
                    if abs(qty - round(qty)) > 0.000001:
                        flash(f'Local PO row {row_number} must use a whole number of rolls.', 'danger')
                        return redirect_to_portal('purchase-orders')
                    if not vendor_item or not is_roll_unit(vendor_item.unit) or parse_numeric(vendor_item.pack_qty) <= 0:
                        flash(f'Add this roll item with meters per roll to vendor {supplier} before creating the Local PO.', 'danger')
                        return redirect_to_portal('purchase-orders')
                    roll_length_m = parse_numeric(vendor_item.pack_qty)
                    rate = rate or parse_numeric(vendor_item.pack_price) or parse_numeric(vendor_item.rate)
                if not item_name or qty <= 0 or rate <= 0:
                    flash(f'Local PO row {row_number} needs an item, quantity, and rate greater than zero.', 'danger')
                    return redirect_to_portal('purchase-orders')
                local_items.append({
                    'item': item_name,
                    'qty': qty,
                    'size': size,
                    'quality': quality,
                    'unit': unit,
                    'roll_length_m': roll_length_m,
                    'rate': rate,
                })

            if not local_items:
                flash('Enter at least one accessory item for the Local PO.', 'danger')
                return redirect_to_portal('purchase-orders')

            po_no = f'LOCAL-{generate_po_no()}'
            sent_at = datetime.utcnow().strftime('%Y-%m-%d')
            for local_item in local_items:
                rate_text = f"{local_item['rate']:.2f}" if local_item['rate'] > 0 else ''
                bill_amount = f"{local_item['qty'] * local_item['rate']:.2f}" if local_item['rate'] > 0 else ''
                db.session.add(SavedRequirement(
                    serial_no=po_no,
                    order_id=LOCAL_ACCESSORY_PO_ORDER_ID,
                    item=local_item['item'],
                    qty=str(local_item['qty']),
                    size=local_item['size'],
                    unit=local_item['unit'],
                    roll_length_m=local_item['roll_length_m'],
                    quality=local_item['quality'],
                    rate=rate_text,
                    bill_amount=bill_amount,
                    supplier=supplier,
                    requested_by=requested_by,
                    priority=priority,
                    date=po_date,
                    for_field='LOCAL STOCK',
                    po_no=po_no,
                    accessory_status='PO_SENT',
                    received_qty='0',
                    issued_qty='0',
                    used_qty='0',
                    po_sent_at=sent_at,
                ))
            db.session.commit()
            flash(f'Local PO {po_no} created and ready for receiving.', 'success')
            return redirect_to_portal('purchase-orders')

        item = SavedRequirement.query.get(request.form.get('item_id'))
        if not item:
            flash('Accessory item not found.', 'danger')
            return redirect_to_portal()
        po_items = SavedRequirement.query.filter_by(order_id=item.order_id, po_no=item.po_no).all()
        current_status = item.accessory_status or 'PENDING'

        if action == 'put_away':
            if is_read_only_profile():
                return reject_read_only_edit('This profile has read-only access to accessory locations.')

            try:
                storage_values = accessory_storage_form_values(request.form)
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect_to_portal('unallocated-stock')
            if not is_whole_stock_quantity(item, storage_values['quantity']):
                flash(f'{item.unit or "Stock"} must be placed away in whole quantities.', 'danger')
                return redirect_to_portal('unallocated-stock')

            unlocated_qty = get_accessory_unlocated_qty(item)
            if storage_values['quantity'] > unlocated_qty + 0.000001:
                flash(
                    f'Cannot put away more than the unlocated balance ({unlocated_qty:g} {item.unit or "PCS"}).',
                    'danger',
                )
                return redirect_to_portal('unallocated-stock')

            location = AccessoryStorageLocation(
                requirement_id=item.id,
                **{key: storage_values[key] for key in (
                    'location_type', 'department', 'gala', 'room', 'rack_no', 'shelf_no',
                    'carton_no', 'description', 'quantity',
                )},
            )
            db.session.add(location)
            db.session.commit()
            flash(
                f'{storage_values["quantity"]:g} {item.unit or "PCS"} of {item.item} placed '
                f'in {accessory_storage_location_label(location)}.',
                'success',
            )
            return redirect_to_portal('unallocated-stock')

        if action == 'return_to_supplier':
            if is_read_only_profile():
                return reject_read_only_edit('This profile has read-only access to accessory stock.')

            return_date = (request.form.get('return_date') or '').strip()
            return_type = (request.form.get('return_type') or 'RETURN').strip().upper()
            returned_qty = parse_numeric(request.form.get('returned_qty'))
            location_id = (request.form.get('storage_location_id') or '').strip()
            if location_id:
                flash('Supplier returns and exchanges are allowed only from unallocated stock.', 'danger')
                return redirect_to_portal('unallocated-stock')
            try:
                datetime.strptime(return_date, '%Y-%m-%d')
            except ValueError:
                flash('Enter a valid supplier return date.', 'danger')
                return redirect_to_portal('unallocated-stock')
            if return_type not in {'RETURN', 'EXCHANGE'}:
                flash('Choose Return or Exchange as the supplier return type.', 'danger')
                return redirect_to_portal('unallocated-stock')
            exchange_item = None
            if return_type == 'EXCHANGE':
                exchange_item_id = (request.form.get('exchange_item_id') or '').strip()
                exchange_item = (
                    db.session.get(ItemMaster, int(exchange_item_id))
                    if exchange_item_id.isdigit() else None
                )
                if not exchange_item:
                    flash('Choose the replacement item from the item list for this exchange.', 'danger')
                    return redirect_to_portal('unallocated-stock')
            if returned_qty <= 0:
                flash('Enter a supplier return quantity greater than zero.', 'danger')
                return redirect_to_portal('unallocated-stock')
            if not is_whole_stock_quantity(item, returned_qty):
                flash(f'{item.unit or "Stock"} must be returned in whole quantities.', 'danger')
                return redirect_to_portal('unallocated-stock')

            available_qty = get_accessory_unlocated_qty(item)

            if returned_qty > available_qty + 0.000001:
                flash(
                    f'Return quantity exceeds the unallocated balance ({available_qty:g} {item.unit or "PCS"}).',
                    'danger',
                )
                return redirect_to_portal('unallocated-stock')

            received_qty = accessory_layer_received_qty(item)
            if returned_qty > received_qty - accessory_layer_issued_qty(item) + 0.000001:
                flash('Only unused accessory stock can be returned to the supplier.', 'danger')
                return redirect_to_portal('unallocated-stock')

            db.session.add(AccessorySupplierReturn(
                requirement_id=item.id,
                storage_location_id=None,
                return_date=return_date,
                returned_by=(session.get('name') or session.get('user') or 'Stock Manager'),
                return_type=return_type,
                returned_qty=returned_qty,
                unit_rate=accessory_receipt_unit_rate(item),
                exchange_item=exchange_item.item_name if exchange_item else '',
                exchange_item_unit=exchange_item.unit if exchange_item else '',
                note=(request.form.get('return_note') or '').strip(),
            ))
            remaining_received = max(0.0, received_qty - returned_qty)
            item.received_qty = str(round(remaining_received, 4))
            net_issued = accessory_layer_issued_qty(item)
            item.issued_qty = str(round(net_issued, 4))
            item.used_qty = str(round(max(0.0, remaining_received - net_issued), 4))
            item.accessory_status = (
                'RETURNED' if remaining_received <= 0.000001
                else 'USED' if net_issued >= remaining_received - 0.000001
                else 'RECEIVED'
            )
            db.session.commit()
            flash(
                f'{returned_qty:g} {item.unit or "PCS"} recorded as {return_type.lower()} to supplier '
                f'for {item.item}. Any replacement must be received separately.',
                'success',
            )
            return redirect_to_portal('unallocated-stock')

        if action == 'move_stock':
            if is_read_only_profile():
                return reject_read_only_edit('This profile has read-only access to accessory locations.')
            source = AccessoryStorageLocation.query.get(request.form.get('source_location_id'))
            if not source or source.requirement_id != item.id:
                flash('Source storage location not found.', 'danger')
                return redirect_to_portal('issuance-store-finder')
            try:
                storage_values = accessory_storage_form_values(request.form)
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect_to_portal('issuance-store-finder')
            if not is_whole_stock_quantity(item, storage_values['quantity']):
                flash(f'{item.unit or "Stock"} must be moved in whole quantities.', 'danger')
                return redirect_to_portal('issuance-store-finder')
            if storage_values['quantity'] > source.quantity + 0.000001:
                flash(
                    f'Cannot move more than the location balance ({source.quantity:g} {item.unit or "PCS"}).',
                    'danger',
                )
                return redirect_to_portal('issuance-store-finder')
            source.quantity = max(0.0, source.quantity - storage_values['quantity'])
            destination = AccessoryStorageLocation(
                requirement_id=item.id,
                **{key: storage_values[key] for key in (
                    'location_type', 'department', 'gala', 'room', 'rack_no', 'shelf_no',
                    'carton_no', 'description', 'quantity',
                )},
            )
            db.session.add(destination)
            db.session.commit()
            flash(
                f'{storage_values["quantity"]:g} {item.unit or "PCS"} moved to '
                f'{accessory_storage_location_label(destination)}.',
                'success',
            )
            return redirect_to_portal('issuance-store-finder')

        if action == 'return_issue':
            if is_read_only_profile():
                return reject_read_only_edit('This profile has read-only access to accessory returns.')
            issue = AccessoryIssue.query.get(request.form.get('issue_id')) if request.form.get('issue_id') else None
            if not issue or issue.requirement_id != item.id:
                flash('Issue entry not found.', 'danger')
                return redirect_to_portal(order_id=request.args.get('order_id') or None)
            if issue not in accessory_layer_issue_entries(item):
                flash('This issue entry predates the current receipt and cannot be returned from it.', 'danger')
                return redirect_to_portal(order_id=issue.order_id or None)
            if not is_accessory_returnable(item.item):
                flash(f'{item.item or "This item"} is not marked as returnable in Item Master.', 'danger')
                return redirect_to_portal(order_id=issue.order_id or None)

            return_date = (request.form.get('return_date') or '').strip()
            returned_by = (session.get('name') or session.get('user') or '').strip()
            returned_qty = parse_numeric(request.form.get('returned_qty'))
            if not is_whole_stock_quantity(item, returned_qty):
                flash(f'{item.unit or "Stock"} must be returned in whole quantities.', 'danger')
                return redirect_to_portal(order_id=issue.order_id or None)
            try:
                datetime.strptime(return_date, '%Y-%m-%d')
            except ValueError:
                flash('Enter a valid return date.', 'danger')
                return redirect_to_portal(order_id=issue.order_id or None)
            remaining_returnable = max(0.0, parse_numeric(issue.issued_qty) - accessory_issue_returned_qty(issue))
            if returned_qty <= 0 or returned_qty > remaining_returnable + 0.000001:
                flash(f'Return quantity must be greater than zero and no more than {remaining_returnable:g}.', 'danger')
                return redirect_to_portal(order_id=issue.order_id or None)

            db.session.add(AccessoryReturn(
                issue_id=issue.id,
                return_date=return_date,
                returned_by=returned_by or 'Stock Manager',
                returned_qty=returned_qty,
                note=(request.form.get('return_note') or '').strip(),
            ))
            if issue.storage_location:
                issue.storage_location.quantity += returned_qty
            db.session.flush()
            db.session.expire(issue, ['return_entries'])
            received_qty = accessory_layer_received_qty(item)
            net_issued = accessory_layer_issued_qty(item)
            item.issued_qty = str(round(net_issued, 4))
            item.used_qty = str(round(max(0.0, received_qty - net_issued), 4))
            item.accessory_status = 'USED' if received_qty > 0 and net_issued >= received_qty else 'RECEIVED'
            db.session.commit()
            flash(f'{returned_qty:g} {item.unit or "units"} returned to accessory stock.', 'success')
            return redirect_to_portal('issued-returned-items', order_id=issue.order_id or None)

        if action == 'save_issue':
            issue_date = (request.form.get('issue_date') or '').strip()
            worker_name = (request.form.get('worker_name') or '').strip()
            order_id = (request.form.get('order_id') or '').strip()
            cut_sheet_id = request.form.get('cut_sheet_id', type=int)
            issued_as_qty = parse_numeric(request.form.get('issued_qty'))
            issued_as_unit = item.issue_unit or item.unit or 'PCS'
            issue_conversion_factor = parse_numeric(item.issue_unit_factor) or 1.0
            issued_qty = accessory_issue_stock_qty(item, issued_as_qty, issued_as_unit)
            if not issue_date or not worker_name or issued_as_qty <= 0:
                flash('Issue date, worker name, and issued quantity are required.', 'danger')
                return redirect_to_portal('issuance-store-finder', order_id=order_id or None)
            if is_discrete_issue_unit(issued_as_unit) and abs(issued_as_qty - round(issued_as_qty)) > 0.000001:
                flash(f'{issued_as_unit} must be issued as a whole quantity.', 'danger')
                return redirect_to_portal('issuance-store-finder', order_id=order_id or None)
            try:
                datetime.strptime(issue_date, '%Y-%m-%d')
            except ValueError:
                flash('Enter a valid issue date.', 'danger')
                return redirect_to_portal('issuance-store-finder', order_id=order_id or None)
            if order_id and not Order.query.filter_by(job_no=order_id).first():
                flash('Selected order was not found.', 'danger')
                return redirect_to_portal('issuance-store-finder')

            cut_sheet = None
            if order_id:
                order = Order.query.filter_by(job_no=order_id).first()
                order_cuts = [
                    sheet for sheet in CuttingSheet.query.filter_by(order_id=order_id).all()
                    if accessory_cut_pcs(sheet) > 0
                ]
                if cut_sheet_id:
                    cut_sheet = CuttingSheet.query.filter_by(
                        id=cut_sheet_id,
                        order_id=order_id,
                    ).first()
                    if not cut_sheet or accessory_cut_pcs(cut_sheet) <= 0:
                        flash('Choose a valid cut for the selected order.', 'danger')
                        return redirect_to_portal('issuance-store-finder', order_id=order_id)
                elif order_cuts:
                    flash('Select the cut this accessory issue belongs to.', 'danger')
                    return redirect_to_portal('issuance-store-finder', order_id=order_id)

                if cut_sheet and (
                    not order.article_id or article_material_spec_for_item(order, item.item)
                ):
                    order_pcs = get_effective_order_quantity(order)
                    if order_pcs <= 0:
                        flash('The selected order has no valid piece quantity.', 'danger')
                        return redirect_to_portal('issuance-store-finder', order_id=order_id)
                    cut_limit = accessory_required_qty_for_cut(item, order, accessory_cut_pcs(cut_sheet))
                    already_issued = sum(
                        max(0.0, parse_numeric(entry.issued_qty) - accessory_issue_returned_qty(entry))
                        for entry in AccessoryIssue.query.filter_by(
                            requirement_id=item.id,
                            order_id=order_id,
                            cut_sheet_id=cut_sheet.id,
                        ).all()
                    )
                    cut_remaining = max(0.0, cut_limit - already_issued)
                    if issued_qty > cut_remaining + 0.000001:
                        flash(
                            f'Issue quantity exceeds this cut allocation ({cut_remaining:g} {item.unit or "PCS"} remaining).',
                            'danger',
                        )
                        return redirect_to_portal('issuance-store-finder', order_id=order_id)

            location = AccessoryStorageLocation.query.get(request.form.get('storage_location_id'))
            if not location or location.requirement_id != item.id:
                flash('Choose a valid storage location for this item.', 'danger')
                return redirect_to_portal('issuance-store-finder', order_id=order_id or None)
            if issued_qty > location.quantity + 0.000001:
                flash(
                    f'Issue quantity exceeds this location balance ({location.quantity:g} {item.unit or "PCS"}).',
                    'danger',
                )
                return redirect_to_portal('issuance-store-finder', order_id=order_id or None)

            db.session.add(AccessoryIssue(
                requirement_id=item.id,
                storage_location_id=location.id,
                order_id=order_id or None,
                cut_no=(cut_sheet.cut_no or str(cut_sheet.id)) if cut_sheet else None,
                cut_sheet_id=cut_sheet.id if cut_sheet else None,
                cutting_pcs=accessory_cut_pcs(cut_sheet) if cut_sheet else None,
                issue_date=issue_date,
                worker_name=worker_name,
                issued_qty=issued_qty,
                issued_as_qty=issued_as_qty,
                issued_as_unit=issued_as_unit,
                issue_conversion_factor=issue_conversion_factor,
                unit_rate=parse_numeric(item.rate),
            ))
            location.quantity = max(0.0, location.quantity - issued_qty)
            db.session.flush()
            db.session.expire(item, ['issue_entries'])
            receipt_issued = accessory_layer_issued_qty(item)
            item.issued_qty = str(round(receipt_issued, 4))
            item.used_qty = str(round(max(0.0, accessory_layer_received_qty(item) - receipt_issued), 4))
            item.accessory_status = (
                'USED' if receipt_issued >= accessory_layer_received_qty(item) else 'RECEIVED'
            )

            db.session.commit()
            flash(
                f'{issued_as_qty:g} {issued_as_unit} issued from {accessory_storage_location_label(location)}.',
                'success',
            )
            return redirect_to_portal('issuance-store-finder', order_id=order_id or None)

        if action in {'edit_issue', 'delete_issue'}:
            if action == 'delete_issue' and (
                session.get('role') not in ('owner', 'manager') or is_read_only_profile()
            ):
                return reject_read_only_edit('Only the owner and manager can delete accessory issue entries.')
            issue = AccessoryIssue.query.get(request.form.get('issue_id')) if request.form.get('issue_id') else None
            if action != 'save_issue' and (not issue or issue.requirement_id != item.id):
                flash('Issue entry not found.', 'danger')
                return redirect_to_portal('issued-returned-items', **request.args)
            if issue and issue not in accessory_layer_issue_entries(item):
                flash('This issue entry predates the current receipt and cannot be changed from it.', 'danger')
                return redirect_to_portal(order_id=issue.order_id or None)

            if action == 'delete_issue':
                if accessory_issue_returned_qty(issue) > 0:
                    flash('An issue with recorded returns cannot be deleted.', 'danger')
                    return redirect_to_portal(order_id=issue.order_id or None)
                if issue.storage_location:
                    issue.storage_location.quantity += issue.issued_qty
                db.session.delete(issue)
            else:
                issue_date = (request.form.get('issue_date') or '').strip()
                worker_name = (request.form.get('worker_name') or '').strip()
                order_id = (request.form.get('order_id') or '').strip()
                cut_sheet_id = request.form.get('cut_sheet_id', type=int)
                issued_as_qty = parse_numeric(request.form.get('issued_qty'))
                issued_as_unit = item.issue_unit or item.unit or 'PCS'
                issue_conversion_factor = parse_numeric(item.issue_unit_factor) or 1.0
                issued_qty = accessory_issue_stock_qty(item, issued_as_qty, issued_as_unit)
                if not issue_date or not worker_name or issued_as_qty <= 0:
                    flash('Issue date, worker name, and issued quantity are required.', 'danger')
                    return redirect_to_portal('issued-returned-items', **request.args)
                if is_discrete_issue_unit(issued_as_unit) and abs(issued_as_qty - round(issued_as_qty)) > 0.000001:
                    flash(f'{issued_as_unit} must be issued as a whole quantity.', 'danger')
                    return redirect_to_portal('issued-returned-items', **request.args)
                if order_id and not Order.query.filter_by(job_no=order_id).first():
                    flash('Selected order was not found.', 'danger')
                    return redirect_to_portal(**request.args)
                cut_sheet = None
                if order_id:
                    order = Order.query.filter_by(job_no=order_id).first()
                    order_cuts = [
                        sheet for sheet in CuttingSheet.query.filter_by(order_id=order_id).all()
                        if accessory_cut_pcs(sheet) > 0
                    ]
                    if cut_sheet_id:
                        cut_sheet = CuttingSheet.query.filter_by(
                            id=cut_sheet_id,
                            order_id=order_id,
                        ).first()
                        if not cut_sheet or accessory_cut_pcs(cut_sheet) <= 0:
                            flash('Choose a valid cut for the selected order.', 'danger')
                            return redirect_to_portal('issued-returned-items', order_id=issue.order_id or None)
                    elif order_cuts:
                        flash('Select the cut this accessory issue belongs to.', 'danger')
                        return redirect_to_portal('issued-returned-items', order_id=issue.order_id or None)

                    if cut_sheet and (
                        not order.article_id or article_material_spec_for_item(order, item.item)
                    ):
                        order_pcs = get_effective_order_quantity(order)
                        if order_pcs <= 0:
                            flash('The selected order has no valid piece quantity.', 'danger')
                            return redirect_to_portal('issued-returned-items', order_id=issue.order_id or None)
                        cut_limit = accessory_required_qty_for_cut(item, order, accessory_cut_pcs(cut_sheet))
                        other_issued = sum(
                            max(0.0, parse_numeric(entry.issued_qty) - accessory_issue_returned_qty(entry))
                            for entry in AccessoryIssue.query.filter_by(
                                requirement_id=item.id,
                                order_id=order_id,
                                cut_sheet_id=cut_sheet.id,
                            ).all()
                            if entry.id != issue.id
                        )
                        requested_net = max(
                            0.0,
                            issued_qty - accessory_issue_returned_qty(issue),
                        )
                        if requested_net > max(0.0, cut_limit - other_issued) + 0.000001:
                            flash(
                                'Issue quantity exceeds the remaining allocation for this cut.',
                                'danger',
                            )
                            return redirect_to_portal('issued-returned-items', order_id=issue.order_id or None)
                if issued_qty + 0.000001 < accessory_issue_returned_qty(issue):
                    flash('Issued quantity cannot be less than the quantity already returned.', 'danger')
                    return redirect_to_portal(order_id=issue.order_id or None)
                if issue.storage_location:
                    location = issue.storage_location
                    if issued_qty > issue.issued_qty + location.quantity + 0.000001:
                        flash(
                            f'Issue quantity exceeds this location balance ({issue.issued_qty + location.quantity:g} {item.unit or "PCS"} including the existing issue).',
                            'danger',
                        )
                        return redirect_to_portal(order_id=issue.order_id or None)
                    location.quantity = max(0.0, location.quantity + issue.issued_qty - issued_qty)
                issue.issue_date = issue_date
                issue.worker_name = worker_name
                issue.issued_qty = issued_qty
                issue.issued_as_qty = issued_as_qty
                issue.issued_as_unit = issued_as_unit
                issue.issue_conversion_factor = issue_conversion_factor
                issue.order_id = order_id or None
                issue.cut_no = (cut_sheet.cut_no or str(cut_sheet.id)) if cut_sheet else None
                issue.cut_sheet_id = cut_sheet.id if cut_sheet else None
                issue.cutting_pcs = accessory_cut_pcs(cut_sheet) if cut_sheet else None
                if issue.unit_rate <= 0:
                    issue.unit_rate = accessory_receipt_unit_rate(item)

            db.session.flush()
            db.session.expire(item, ['issue_entries'])
            received_qty = accessory_layer_received_qty(item)
            issue_entries = accessory_layer_issue_entries(item)
            gross_issued = sum(
                parse_numeric(entry.issued_qty)
                for entry in issue_entries
            )
            total_returned = sum(
                accessory_issue_returned_qty(entry)
                for entry in issue_entries
            )
            if gross_issued > received_qty + 0.000001:
                db.session.rollback()
                flash('Issued quantity cannot be greater than the received quantity.', 'danger')
                return redirect_to_portal(**request.args)
            total_issued = max(0.0, gross_issued - total_returned)
            item.issued_qty = str(round(total_issued, 4))
            item.used_qty = str(round(max(0.0, received_qty - total_issued), 4))
            item.accessory_status = 'USED' if received_qty > 0 and total_issued >= received_qty else 'RECEIVED'
            db.session.commit()
            flash('Issue entry saved.' if action != 'delete_issue' else 'Issue entry deleted.', 'success')
            return redirect_to_portal('issued-returned-items', **request.args)

        if action == 'mark_po_sent' and current_status == 'PENDING':
            item.accessory_status = 'PO_SENT'
            item.po_sent_at = datetime.utcnow().strftime('%Y-%m-%d')
            flash(f'Purchase order marked as sent for {item.item}.', 'success')
        elif action == 'mark_received' and current_status in {'PO_SENT', 'PENDING'}:
            uploaded_image = request.files.get('purchase_slip_image')
            if not uploaded_image or not uploaded_image.filename:
                flash('Attach the purchase slip picture before receiving this PO.', 'danger')
                return redirect_to_portal(**request.args)

            extension = uploaded_image.filename.rsplit('.', 1)[-1].lower() if '.' in uploaded_image.filename else ''
            if extension not in {'png', 'jpg', 'jpeg', 'webp'}:
                flash('Purchase slip must be a PNG, JPG, JPEG, or WEBP image.', 'danger')
                return redirect_to_portal(**request.args)

            receipt_values = []
            for po_item in po_items:
                received_field = f'received_qty_{po_item.id}'
                received_qty = parse_numeric(request.form.get(received_field, po_item.qty))
                if received_qty <= 0 or received_qty > parse_numeric(po_item.qty) + 0.000001:
                    flash(f'Enter a received quantity from 0 to the PO quantity for {po_item.item}.', 'danger')
                    return redirect_to_portal(**request.args)

                issue_unit = (request.form.get(f'issue_unit_{po_item.id}') or po_item.issue_unit or po_item.unit or '').strip().upper()
                stock_unit = (po_item.unit or '').strip()
                factor_text = (request.form.get(f'issue_factor_{po_item.id}') or '').strip()
                entered_factor = parse_numeric(factor_text)
                factor_mode = (request.form.get(f'issue_factor_mode_{po_item.id}') or 'STOCK_PER_ISSUE').strip().upper()
                issue_factor = entered_factor
                roll_length_m = 0.0
                if issue_unit.casefold() == stock_unit.casefold():
                    issue_factor = 1.0
                elif factor_text and issue_factor <= 0:
                    flash(f'Enter a positive PO-unit conversion for {po_item.item}.', 'danger')
                    return redirect_to_portal(**request.args)
                elif factor_text and factor_mode == 'ISSUE_PER_STOCK':
                    issue_factor = 1.0 / entered_factor
                elif not factor_text:
                    if is_roll_unit(issue_unit):
                        old_roll_length = parse_numeric(request.form.get(f'issue_roll_length_{po_item.id}'))
                        stock_unit_meters = length_to_meters(1, stock_unit)
                        if old_roll_length > 0 and stock_unit_meters > 0:
                            issue_factor = old_roll_length / stock_unit_meters
                        elif parse_numeric(po_item.issue_unit_factor) > 0:
                            issue_factor = parse_numeric(po_item.issue_unit_factor)
                    elif issue_unit.casefold() in {'pcs', 'pc'} and stock_unit.casefold() in {'pack', 'packs'}:
                        pieces_per_pack = parse_numeric(request.form.get(f'issue_pieces_per_pack_{po_item.id}'))
                        if pieces_per_pack > 0:
                            issue_factor = 1.0 / pieces_per_pack
                    if issue_factor <= 0:
                        issue_factor = unit_conversion_factor(stock_unit, issue_unit) or 0.0
                if issue_factor <= 0:
                    flash(
                        f'Enter how many {stock_unit or "PO units"} are used by one {issue_unit or "issue unit"} for {po_item.item}.',
                        'danger',
                    )
                    return redirect_to_portal(**request.args)
                if is_roll_unit(issue_unit):
                    roll_length_m = length_to_meters(issue_factor, stock_unit)
                receipt_values.append((po_item, received_qty, issue_unit, issue_factor, roll_length_m))

            filename = secure_filename(uploaded_image.filename)
            filename = f"purchase-slip-{item.po_no or item.id}-{datetime.utcnow().strftime('%Y%m%d%H%M%S%f')}-{filename}"
            uploaded_image.save(os.path.join(app.config['UPLOAD_FOLDER'], filename))
            image_path = url_for('static', filename=f'uploads/{filename}')
            received_date = datetime.utcnow().strftime('%Y-%m-%d')
            for po_item, received_qty, issue_unit, issue_factor, roll_length_m in receipt_values:
                po_item.received_qty = str(received_qty)
                po_item.issue_unit = issue_unit
                po_item.issue_unit_factor = issue_factor
                if roll_length_m > 0:
                    po_item.roll_length_m = roll_length_m
                po_item.accessory_status = 'RECEIVED'
                po_item.received_at = received_date
                po_item.purchase_slip_image = image_path
            flash(f'All items in PO {item.po_no or ""} marked as received.', 'success')
        db.session.commit()
        target_page = (
            'unallocated-stock' if action == 'mark_received'
            else 'purchase-orders' if action == 'mark_po_sent'
            else None
        )
        return redirect_to_portal(target_page, **request.args)

    status_filter = (request.args.get('status') or '').strip()
    search = (request.args.get('search') or '').strip()
    selected_order_id = (request.args.get('order_id') or '').strip()
    vendors = Vendor.query.order_by(Vendor.name.asc()).all()
    departments = Department.query.order_by(func.lower(Department.name)).all()
    department_store_rooms = {
        department.name.casefold(): sorted(
            store_room.name for store_room in department.store_rooms
        )
        for department in departments
    }
    local_po_items = ItemMaster.query.order_by(ItemMaster.item_name.asc()).all()
    issue_orders = Order.query.order_by(Order.id.desc()).all()
    issue_article_ids = {order.article_id for order in issue_orders if order.article_id}
    issue_article_material_items = {}
    if issue_article_ids:
        for spec in ArticleMaterialSpec.query.filter(
            ArticleMaterialSpec.article_id.in_(issue_article_ids)
        ).all():
            issue_article_material_items.setdefault(str(spec.article_id), []).append(spec.item_name or '')
    party_accessories = PartySuppliedAccessory.query.order_by(
        PartySuppliedAccessory.sent_date.desc(), PartySuppliedAccessory.id.desc()
    ).all()
    stock_positions = get_accessory_stock_positions()
    storage_rows = get_accessory_storage_rows()
    storage_rows = [
        row for row in storage_rows
        if parse_numeric(row['location'].quantity) > 0.000001
    ]
    location_search = (request.args.get('location_search') or '').strip()
    if location_search:
        location_term = location_search.casefold()
        storage_rows = [
            row for row in storage_rows
            if location_term in ' '.join((
                row['item'],
                row['size'],
                row['quality'],
                row['unit'],
                row['label'],
                row['description'],
                row['location'].requirement.po_no or '',
                row['location'].requirement.supplier or '',
            )).casefold()
        ]
    storage_location_groups = {}
    for row in storage_rows:
        location = row['location']
        group_key = tuple(
            (str(value or '').strip().casefold())
            for value in (
                row['item'], row['size'], row['quality'], location.location_type,
                location.department, location.gala, location.room, location.rack_no,
                location.shelf_no, location.carton_no,
            )
        )
        location_group = storage_location_groups.setdefault(group_key, {
            'item': row['item'],
            'size': row['size'],
            'quality': row['quality'],
            'label': row['label'],
            'layers': [],
            'available_by_unit': {},
            'available_by_issue_unit': {},
        })
        location_group['layers'].append(row)
        unit = (row['unit'] or 'PCS').strip().upper()
        unit_total = location_group['available_by_unit'].setdefault(unit, 0.0)
        location_group['available_by_unit'][unit] = unit_total + parse_numeric(location.quantity)
        issue_unit = (row['issue_unit'] or unit).strip().upper()
        issue_factor = parse_numeric(row['issue_unit_factor']) or 1.0
        if issue_unit.casefold() != unit.casefold() and issue_factor > 0:
            issue_key = (unit, issue_unit, issue_factor)
            issue_total = location_group['available_by_issue_unit'].setdefault(issue_key, 0.0)
            location_group['available_by_issue_unit'][issue_key] = (
                issue_total + parse_numeric(location.quantity) / issue_factor
            )

    storage_item_groups = {}
    for location_group in storage_location_groups.values():
        location_group['layers'].sort(key=lambda row: (
            (row['location'].requirement.received_at or row['location'].requirement.date or '') if row['location'].requirement else '',
            row['location'].requirement.po_no if row['location'].requirement else '',
            row['location'].id or 0,
        ))
        location_group['available_by_unit'] = sorted(
            location_group['available_by_unit'].items(), key=lambda entry: entry[0].casefold()
        )
        location_group['available_by_issue_unit'] = sorted(
            location_group['available_by_issue_unit'].items(),
            key=lambda entry: (entry[0][1].casefold(), entry[0][2]),
        )
        storage_item_groups.setdefault(location_group['item'], []).append(location_group)
    storage_item_groups = [
        {
            'item': item_name,
            'locations': sorted(
                location_groups,
                key=lambda group: (group['size'].casefold(), group['quality'].casefold(), group['label'].casefold()),
            ),
        }
        for item_name, location_groups in sorted(storage_item_groups.items(), key=lambda entry: entry[0].casefold())
    ]
    put_away_items = []
    for received_item in SavedRequirement.query.order_by(SavedRequirement.id.desc()).all():
        received_item.received_value = accessory_layer_received_qty(received_item)
        received_item.unlocated_qty = get_accessory_unlocated_qty(received_item)
        if received_item.received_value > 0 and received_item.unlocated_qty > 0.000001:
            put_away_items.append(received_item)
    query = SavedRequirement.query
    if status_filter:
        if status_filter == 'PENDING':
            query = query.filter(or_(SavedRequirement.accessory_status.is_(None), SavedRequirement.accessory_status == 'PENDING'))
        else:
            query = query.filter_by(accessory_status=status_filter)
    if search:
        like = f"%{search.lower()}%"
        query = query.filter(or_(
            func.lower(SavedRequirement.item).like(like),
            func.lower(SavedRequirement.order_id).like(like),
            func.lower(SavedRequirement.supplier).like(like),
            func.lower(SavedRequirement.po_no).like(like),
        ))
    items = query.order_by(SavedRequirement.id.desc()).all()
    status_updates = False
    for item in items:
        item.status_display = item.accessory_status or 'PENDING'
        item.qty_value = parse_numeric(item.qty)
        item.received_value = accessory_layer_received_qty(item)
        item.issue_history_entries = accessory_layer_issue_entries(item)
        issue_history_total = sum(parse_numeric(entry.issued_qty) for entry in item.issue_history_entries)
        item.issued_value = issue_history_total if item.issue_entries else parse_numeric(item.issued_qty)
        item.returned_value = sum(accessory_issue_returned_qty(entry) for entry in item.issue_history_entries)
        item.net_issued_value = max(0.0, item.issued_value - item.returned_value)
        item.left_over_value = max(0.0, item.received_value - item.net_issued_value)
        item.issue_form_date = datetime.utcnow().strftime('%Y-%m-%d')
        item.returnable = is_accessory_returnable(item.item)
        for issue_entry in item.issue_history_entries:
            issue_entry.returned_value = accessory_issue_returned_qty(issue_entry)
            issue_entry.returnable = item.returnable
            issue_entry.returnable_remaining_qty = max(0.0, issue_entry.issued_qty - issue_entry.returned_value)
            issue_entry.location_label = (
                accessory_storage_location_label(issue_entry.storage_location)
                if issue_entry.storage_location else 'Location not recorded'
            )
            issue_entry.editable_max_qty = (
                issue_entry.issued_qty + issue_entry.storage_location.quantity
                if issue_entry.storage_location else item.left_over_value + issue_entry.issued_qty
            )
        if item.received_value > 0 and item.net_issued_value >= item.received_value:
            if item.accessory_status != 'USED':
                status_updates = True
            item.accessory_status = 'USED'
            item.status_display = 'USED'
            item.left_over_value = 0.0
        elif item.accessory_status == 'USED' and item.net_issued_value < item.received_value:
            item.accessory_status = 'RECEIVED'
            item.status_display = 'RECEIVED'
            status_updates = True

    if status_updates:
        db.session.commit()

    received_item_groups = get_accessory_received_history_groups(items)
    supplier_returns = AccessorySupplierReturn.query.order_by(
        AccessorySupplierReturn.id.desc()
    ).limit(250).all()
    for supplier_return in supplier_returns:
        supplier_return.location_label = (
            accessory_storage_location_label(supplier_return.storage_location)
            if supplier_return.storage_location else 'Unlocated stock'
        )

    po_groups = {}
    for po_item in SavedRequirement.query.order_by(SavedRequirement.id.desc()).all():
        if is_party_supplied_stock_layer(po_item):
            continue
        if not (po_item.issue_unit or '').strip():
            po_item.issue_unit = default_issue_unit_for_item(po_item.item, po_item.unit or 'PCS')
        group_key = (po_item.order_id or '', po_item.po_no or '')
        po_groups.setdefault(group_key, []).append(po_item)

    auto_po_summaries = []
    local_po_summaries = []
    for (order_id, po_no), group_items in sorted(po_groups.items(), key=lambda group: (group[0][0], group[0][1])):
        display_statuses = [
            'PO_SENT' if (po_item.accessory_status or 'PENDING') == 'PENDING'
            else (po_item.accessory_status or 'PENDING')
            for po_item in group_items
        ]
        unique_statuses = set(display_statuses)
        all_received = bool(group_items) and all(accessory_layer_received_qty(po_item) > 0 for po_item in group_items)
        po_status = display_statuses[0] if len(unique_statuses) == 1 else 'IN PROGRESS'
        po_summary = {
            'order_id': 'LOCAL STOCK' if order_id == LOCAL_ACCESSORY_PO_ORDER_ID else (order_id or '-'),
            'is_local': order_id == LOCAL_ACCESSORY_PO_ORDER_ID,
            'po_no': po_no or '-',
            'status': po_status,
            'item_id': group_items[0].id if group_items else '',
            'all_received': all_received,
            'receipt_image': next((po_item.purchase_slip_image for po_item in group_items if po_item.purchase_slip_image), ''),
            'items': group_items,
        }
        if order_id == LOCAL_ACCESSORY_PO_ORDER_ID:
            local_po_summaries.append(po_summary)
        else:
            auto_po_summaries.append(po_summary)

    def purchase_order_sort_key(po):
        dates = [normalize_date(item.date) for item in po['items']]
        latest_date = max((date for date in dates if date), default=datetime.min)
        latest_id = max((item.id or 0 for item in po['items']), default=0)
        return latest_date, latest_id

    auto_po_summaries.sort(key=purchase_order_sort_key, reverse=True)
    local_po_summaries.sort(key=purchase_order_sort_key, reverse=True)

    po_view_data = {}
    for po in auto_po_summaries + local_po_summaries:
        first_item = po['items'][0] if po['items'] else None
        po_lines = []
        po_total = 0.0
        for po_item in po['items']:
            quantity = parse_numeric(po_item.qty)
            rate = parse_numeric(po_item.rate)
            line_amount = parse_numeric(po_item.bill_amount)
            if line_amount <= 0 and quantity > 0 and rate > 0:
                line_amount = quantity * rate
            po_total += line_amount
            po_lines.append({
                'item': po_item.item or 'UNSPECIFIED',
                'size': po_item.size or '',
                'quality': po_item.quality or '',
                'quantity': po_item.qty or '',
                'unit': po_item.unit or 'PCS',
                'rate': rate,
                'amount': line_amount,
            })
        po_view_data[str(po['item_id'])] = {
            'po_no': po['po_no'],
            'order_id': po['order_id'],
            'status': 'RECEIVED' if po['all_received'] else po['status'],
            'supplier': first_item.supplier or '' if first_item else '',
            'date': first_item.date or '' if first_item else '',
            'requested_by': first_item.requested_by or '' if first_item else '',
            'priority': first_item.priority or '' if first_item else '',
            'for_field': first_item.for_field or '' if first_item else '',
            'serial_no': first_item.serial_no or '' if first_item else '',
            'is_local': po['is_local'],
            'items': po_lines,
            'total': po_total,
        }

    return render_template(
        'accessories.html', items=items, received_item_groups=received_item_groups,
        portal_page=portal_page,
        status_filter=status_filter, search=search,
        accessory_summary=get_accessory_stock_summary(),
        auto_po_summaries=auto_po_summaries, local_po_summaries=local_po_summaries,
        po_view_data=po_view_data,
        vendors=vendors, departments=departments,
        department_store_rooms=department_store_rooms,
        local_po_items=local_po_items,
        local_po_order_id=LOCAL_ACCESSORY_PO_ORDER_ID,
        local_po_today=datetime.now().strftime('%Y-%m-%d'),
        issue_article_material_items=issue_article_material_items,
        stock_positions=stock_positions, storage_rows=storage_rows,
        storage_item_groups=storage_item_groups,
        storage_location_count=len(storage_location_groups),
        put_away_items=put_away_items, location_search=location_search,
        issue_orders=issue_orders,
        party_accessories=party_accessories,
        selected_order_id=selected_order_id,
        supplier_returns=supplier_returns,
    )


@app.route('/stock-portal/accessories/supplier-return/<int:return_id>/print')
def accessory_supplier_return_print(return_id):
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    supplier_return = db.session.get(AccessorySupplierReturn, return_id)
    if not supplier_return:
        abort(404)

    return render_template(
        'accessory_supplier_return_print.html',
        supplier_return=supplier_return,
        location_label=(
            accessory_storage_location_label(supplier_return.storage_location)
            if supplier_return.storage_location else 'Unallocated stock'
        ),
    )


@app.route('/stock-portal/warehouse')
def warehouse_portal():
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    ready_orders = []
    for order in Order.query.order_by(Order.id.desc()).all():
        if not order.job_no:
            continue
        shipping = warehouse_finished_goods_snapshot(
            order, get_order_shipping_snapshot(order)
        )
        if shipping['dispatchable_pcs'] > 0.000001:
            ready_orders.append({'order': order, **shipping})
    ready_a_return_shipments = [
        inventory for inventory in Inventory.query.filter_by(
            a_returned_to_party=True,
            a_returned_shipped=False,
        ).order_by(Inventory.id.desc()).all()
        if parse_numeric(inventory.a_returned_quantity) > 0
    ]
    ready_b_return_shipments = [
        inventory for inventory in Inventory.query.filter_by(
            b_returned_to_party=True,
            b_returned_shipped=False,
        ).order_by(Inventory.id.desc()).all()
        if parse_numeric(inventory.b_returned_quantity) > 0
    ]
    db.session.commit()
    return render_template(
        'warehouse.html', fabric_totals=get_fabric_stock_totals(),
        accessory_summary=get_accessory_stock_summary(), ready_orders=ready_orders,
        ready_a_return_shipments=ready_a_return_shipments,
        ready_b_return_shipments=ready_b_return_shipments,
    )


@app.route('/stock-portal/warehouse/in-transit', methods=['GET', 'POST'])
def warehouse_in_transit():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    if request.method == 'POST':
        if is_read_only_profile():
            return reject_read_only_edit('This profile has read-only access to warehouse stock locations.')

        order = Order.query.filter_by(job_no=(request.form.get('order_id') or '').strip()).first()
        quality = (request.form.get('quality') or '').strip().upper()
        department_name = (request.form.get('department') or '').strip()
        location_type = (request.form.get('location_type') or '').strip().upper()
        gala = (request.form.get('gala') or '').strip()
        quantity = parse_numeric(request.form.get('quantity'))

        if not order or quality not in {'AQ', 'BQ'}:
            flash('Choose a valid order and quality for warehouse placement.', 'danger')
            return redirect(url_for('warehouse_in_transit'))
        if location_type not in {'RACK_SHELF', 'FLOOR', 'CABINET', 'CUPBOARD'}:
            flash('Choose a valid warehouse location type.', 'danger')
            return redirect(url_for('warehouse_in_transit'))
        department = Department.query.filter(
            func.lower(func.trim(Department.name)) == department_name.casefold()
        ).first()
        if not department:
            flash('Choose a valid department for warehouse placement.', 'danger')
            return redirect(url_for('warehouse_in_transit'))
        if quantity <= 0:
            flash('Enter a quantity greater than zero.', 'danger')
            return redirect(url_for('warehouse_in_transit'))

        shipping = get_order_shipping_snapshot(order)
        quality_balance = (
            shipping['balance_aq_pcs'] if quality == 'AQ'
            else shipping['balance_bq_pcs']
        )
        located = warehouse_finished_goods_by_quality(order.job_no)[quality]
        transit_qty = max(0.0, quality_balance - located)
        if quantity > transit_qty + 0.000001:
            flash(
                f'Cannot place more than the {transit_qty:g} {quality} PCS currently in transit.',
                'danger',
            )
            return redirect(url_for('warehouse_in_transit'))

        db.session.add(WarehouseFinishedGoodsLocation(
            order_id=order.job_no,
            quality=quality,
            location_type=location_type,
            department=department.name,
            room='',
            gala=gala,
            rack_no='',
            shelf_no='',
            quantity=quantity,
        ))
        db.session.commit()
        flash(f'{quantity:g} {quality} PCS from {order.job_no} placed in the warehouse.', 'success')
        return redirect(url_for('warehouse_in_transit'))

    departments = Department.query.order_by(func.lower(Department.name)).all()
    department_store_rooms = {
        department.name.casefold(): [room.name for room in department.store_rooms]
        for department in departments
    }
    transit_rows = []
    for order in Order.query.order_by(Order.id.desc()).all():
        if not order.job_no:
            continue
        shipping = warehouse_finished_goods_snapshot(
            order, get_order_shipping_snapshot(order)
        )
        pcs_per_packet = parse_numeric(order.pcs_poly)
        for quality, produced_key, balance_key, located_key in (
            ('AQ', 'total_aq_pcs', 'balance_aq_pcs', 'warehouse_aq_pcs'),
            ('BQ', 'total_bq_pcs', 'balance_bq_pcs', 'warehouse_bq_pcs'),
        ):
            transit_qty = max(0.0, shipping[balance_key] - shipping[located_key])
            if transit_qty <= 0.000001:
                continue
            transit_rows.append({
                'order': order,
                'quality': quality,
                'produced_pcs': shipping[produced_key],
                'transit_pcs': transit_qty,
                'transit_packets': transit_qty / pcs_per_packet if pcs_per_packet > 0 else 0.0,
            })
    placed_locations = WarehouseFinishedGoodsLocation.query.filter(
        WarehouseFinishedGoodsLocation.quantity > 0
    ).order_by(WarehouseFinishedGoodsLocation.id.desc()).all()
    orders_by_job = {
        order.job_no: order for order in Order.query.filter(
            Order.job_no.in_({location.order_id for location in placed_locations})
        ).all()
    } if placed_locations else {}
    warehouse_locations = [
        {
            'location': location,
            'order': orders_by_job.get(location.order_id),
            'can_relocate': WarehouseFinishedGoodsDispatch.query.filter_by(
                location_id=location.id
            ).first() is None,
            'packets': (
                location.quantity / parse_numeric(orders_by_job[location.order_id].pcs_poly)
                if location.order_id in orders_by_job
                and parse_numeric(orders_by_job[location.order_id].pcs_poly) > 0
                else 0.0
            ),
        }
        for location in placed_locations
    ]
    return render_template(
        'warehouse_in_transit.html',
        transit_rows=transit_rows,
        warehouse_locations=warehouse_locations,
        departments=departments,
        department_store_rooms=department_store_rooms,
    )


@app.route('/stock-portal/warehouse/location/<int:location_id>/relocate', methods=['POST'])
def relocate_warehouse_finished_goods(location_id):
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    if is_read_only_profile():
        return reject_read_only_edit('This profile has read-only access to warehouse stock locations.')

    location = WarehouseFinishedGoodsLocation.query.get_or_404(location_id)
    if location.quantity <= 0:
        flash('This warehouse location has no remaining stock to relocate.', 'warning')
        return redirect(url_for('warehouse_in_transit'))
    if WarehouseFinishedGoodsDispatch.query.filter_by(location_id=location.id).first():
        flash('This stock has already been shipped and can no longer be relocated.', 'danger')
        return redirect(url_for('warehouse_in_transit'))

    department_name = (request.form.get('department') or '').strip()
    room_name = (request.form.get('room') or '').strip()
    location_type = (request.form.get('location_type') or '').strip().upper()
    department = Department.query.filter(
        func.lower(func.trim(Department.name)) == department_name.casefold()
    ).first()
    store_room = DepartmentStoreRoom.query.join(Department).filter(
        func.lower(func.trim(Department.name)) == department_name.casefold(),
        func.lower(func.trim(DepartmentStoreRoom.name)) == room_name.casefold(),
    ).first()
    if not department or not store_room:
        flash('Choose a store room configured for the selected department.', 'danger')
        return redirect(url_for('warehouse_in_transit'))
    if location_type not in {'RACK_SHELF', 'FLOOR', 'CABINET', 'CUPBOARD'}:
        flash('Choose a valid warehouse location type.', 'danger')
        return redirect(url_for('warehouse_in_transit'))

    rack_no = (request.form.get('rack_no') or '').strip()
    shelf_no = (request.form.get('shelf_no') or '').strip()
    if location_type == 'RACK_SHELF' and (not rack_no or not shelf_no):
        flash('Enter both rack and shelf numbers for a Rack/Shelf location.', 'danger')
        return redirect(url_for('warehouse_in_transit'))
    if location_type != 'RACK_SHELF':
        rack_no = ''
        shelf_no = ''

    location.department = department.name
    location.room = store_room.name
    location.location_type = location_type
    location.gala = (request.form.get('gala') or '').strip()
    location.rack_no = rack_no
    location.shelf_no = shelf_no
    db.session.commit()
    flash(
        f'{location.quantity:g} {location.quality} PCS from {location.order_id} relocated.',
        'success',
    )
    return redirect(url_for('warehouse_in_transit'))


def get_inventory_return_quality(inventory):
    a_qty = parse_numeric(getattr(inventory, 'a_returned_quantity', 0))
    b_qty = parse_numeric(getattr(inventory, 'b_returned_quantity', 0))
    if getattr(inventory, 'a_returned_to_party', False) or a_qty > 0:
        return 'a'
    if getattr(inventory, 'b_returned_to_party', False) or b_qty > 0:
        return 'b'

    if getattr(inventory, 'id', None):
        challan = ChallanRecord.query.filter_by(inventory_id=inventory.id).filter(
            ChallanRecord.source_type.in_(['inventory_return_a', 'inventory_return'])
        ).order_by(ChallanRecord.id.desc()).first()
        if challan:
            return 'a' if challan.source_type == 'inventory_return_a' else 'b'

    return 'b' if b_qty >= a_qty else 'a'


@app.route('/stock-portal/warehouse/mark-return-shipped/<int:inventory_id>', methods=['POST'])
def mark_return_shipped(inventory_id):
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    inventory = Inventory.query.get_or_404(inventory_id)
    shipped_by_party = (request.form.get('shipped_by_party') or 'Canon').strip().title()
    if shipped_by_party not in ('Canon', 'Haram'):
        shipped_by_party = 'Canon'

    return_quality = (request.form.get('return_quality') or '').strip().lower()
    if return_quality not in {'a', 'b'}:
        return_quality = get_inventory_return_quality(inventory)
    if return_quality == 'a':
        if parse_numeric(inventory.a_returned_quantity) <= 0 and not inventory.a_returned_to_party:
            flash('This returned fabric is no longer waiting for shipment.', 'warning')
            return redirect(url_for('warehouse_portal'))
        inventory.a_returned_shipped = True
        inventory.a_returned_shipped_by = shipped_by_party
        inventory.a_returned_shipped_date = datetime.utcnow().strftime('%Y-%m-%d')
        source_type = 'inventory_return_a'
        quantity = parse_numeric(inventory.a_returned_quantity)
        party_name = inventory.a_returned_party or ''
        article_name = inventory.a_returned_article or inventory.fabric_for or ''
    elif return_quality == 'b':
        if parse_numeric(inventory.b_returned_quantity) <= 0 and not inventory.b_returned_to_party:
            flash('This returned fabric is no longer waiting for shipment.', 'warning')
            return redirect(url_for('warehouse_portal'))
        inventory.b_returned_shipped = True
        inventory.b_returned_shipped_by = shipped_by_party
        inventory.b_returned_shipped_date = datetime.utcnow().strftime('%Y-%m-%d')
        source_type = 'inventory_return'
        quantity = parse_numeric(inventory.b_returned_quantity)
        party_name = inventory.b_returned_party or ''
        article_name = inventory.b_returned_article or inventory.fabric_for or ''
    else:
        flash('This returned fabric is no longer waiting for shipment.', 'warning')
        return redirect(url_for('warehouse_portal'))

    if not ChallanRecord.query.filter_by(inventory_id=inventory.id, source_type=source_type).first():
        db.session.add(ChallanRecord(
            challan_no=next_challan_number(shipped_by_party),
            source_type=source_type,
            inventory_id=inventory.id,
            job_no=f"RETURNED-{inventory.serial_no or inventory.id}",
            party_name=party_name,
            article_name=article_name,
            challan_date=inventory.a_returned_shipped_date if source_type == 'inventory_return_a' else inventory.b_returned_shipped_date,
            shipped_meter=quantity,
            shipped_by_party=shipped_by_party,
            created_by=session.get('name') or session.get('user') or '',
        ))
    db.session.commit()
    flash(f'Returned shipment marked as shipped by {shipped_by_party}.', 'success')
    return redirect(url_for('challan_portal', shipper=shipped_by_party))


@app.route('/stock-portal/goods-delivery')
def goods_delivery_portal():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    def shipment_value(item, key, default=0.0):
        if isinstance(item, dict):
            return parse_numeric(item.get(key, default))
        return parse_numeric(getattr(item, key, default))

    delivered = []
    for order in Order.query.order_by(Order.id.desc()).all():
        shipments = ShipmentRecord.query.filter_by(order_id=order.id).order_by(ShipmentRecord.id.desc()).all()
        legacy_total = parse_numeric(order.shipped_pcs)

        if not shipments and legacy_total <= 0:
            continue

        if not shipments and legacy_total > 0:
            shipments = [{
                'id': None,
                'job_no': order.job_no,
                'shipped_at': order.shipped_at or order.delivered_at or order.date,
                'shipped_by': order.shipped_by or order.delivered_by or '',
                'shipped_aq_pcs': parse_numeric(order.shipped_aq_pcs),
                'shipped_bq_pcs': parse_numeric(order.shipped_bq_pcs),
                'shipped_aq_packets': parse_numeric(order.shipped_aq_pcs) / parse_numeric(order.pcs_poly) if parse_numeric(order.pcs_poly) > 0 else 0.0,
                'shipped_bq_packets': parse_numeric(order.shipped_bq_pcs) / parse_numeric(order.pcs_poly) if parse_numeric(order.pcs_poly) > 0 else 0.0,
                'shipped_aq_ctn': 0.0,
                'shipped_bq_ctn': 0.0,
                'shipped_aq_bails': 0.0,
                'shipped_bq_bails': 0.0,
                'shipped_pcs': legacy_total,
                'shipped_packets': parse_numeric(order.shipped_packets),
                'shipped_ctn': parse_numeric(order.shipped_ctn),
                'shipped_bails': parse_numeric(order.shipped_bails),
                'ctn_percent': 0.0,
                'bail_percent': 0.0,
            }]

        pcs_per_packet = parse_numeric(order.pcs_poly)
        for shipment in shipments:
            get_value = (
                (lambda key: parse_numeric(shipment.get(key, 0)))
                if isinstance(shipment, dict)
                else (lambda key: parse_numeric(getattr(shipment, key, 0)))
            )
            if pcs_per_packet > 0 and get_value('shipped_aq_packets') <= 0 and not isinstance(shipment, dict):
                shipment.shipped_aq_packets = get_value('shipped_aq_pcs') / pcs_per_packet
            if pcs_per_packet > 0 and get_value('shipped_bq_packets') <= 0 and not isinstance(shipment, dict):
                shipment.shipped_bq_packets = get_value('shipped_bq_pcs') / pcs_per_packet
            if get_value('shipped_packets') <= 0 and not isinstance(shipment, dict):
                shipment.shipped_packets = get_value('shipped_aq_packets') + get_value('shipped_bq_packets')

            quality_units = {}
            for quality in ('aq', 'bq'):
                quality_pcs = get_value(f'shipped_{quality}_pcs')
                quality_packets = get_value(f'shipped_{quality}_packets')
                quality_ctn = get_value(f'shipped_{quality}_ctn')
                quality_bails = get_value(f'shipped_{quality}_bails')
                quality_units[f'shipped_{quality}_direct_pcs'] = max(
                    0.0,
                    quality_pcs
                    - quality_packets * pcs_per_packet
                    - quality_ctn * parse_numeric(order.qty_ctn) * pcs_per_packet
                    - quality_bails * parse_numeric(order.qty_bail) * pcs_per_packet,
                )
            if isinstance(shipment, dict):
                shipment.update(quality_units)
            else:
                for key, value in quality_units.items():
                    setattr(shipment, key, value)

        total_shipped_pcs = sum(shipment_value(s, 'shipped_pcs') for s in shipments)
        total_shipped_packets = sum(shipment_value(s, 'shipped_packets') for s in shipments)
        shipping = get_order_shipping_snapshot(order)
        completed_pcs = shipping['completed_pcs']
        total_order_pcs = shipping['total_order_pcs']
        first_shipment = shipments[0]
        first_date = shipment_value(first_shipment, 'shipped_at', '') if not isinstance(first_shipment, dict) else first_shipment.get('shipped_at', '')
        first_by = shipment_value(first_shipment, 'shipped_by', '') if not isinstance(first_shipment, dict) else first_shipment.get('shipped_by', '')

        if total_order_pcs > 0 and total_shipped_pcs >= total_order_pcs:
            order.fulfillment_status = 'DELIVERED'
        elif total_shipped_pcs > 0:
            order.fulfillment_status = 'PARTIALLY DELIVERED'
        else:
            order.fulfillment_status = 'PENDING'

        order.delivered_at = order.delivered_at or first_date or datetime.utcnow().strftime('%Y-%m-%d')
        order.delivered_by = order.delivered_by or first_by or session.get('name') or session.get('user')
        order.shipped_pcs = f'{total_shipped_pcs:.2f}'
        order.shipped_aq_pcs = f'{sum(shipment_value(s, "shipped_aq_pcs") for s in shipments):.2f}'
        order.shipped_bq_pcs = f'{sum(shipment_value(s, "shipped_bq_pcs") for s in shipments):.2f}'
        order.shipped_packets = f'{sum(shipment_value(s, "shipped_packets") for s in shipments):.2f}'
        order.shipped_ctn = f'{sum(shipment_value(s, "shipped_ctn") for s in shipments):.2f}'
        order.shipped_bails = f'{sum(shipment_value(s, "shipped_bails") for s in shipments):.2f}'

        delivered.append({
            'kind': 'order',
            'order': order,
            'shipments': shipments,
            'total_shipped_pcs': total_shipped_pcs,
            'total_shipped_packets': total_shipped_packets,
        })

    for quality, returned_inventories in (
        ('a', Inventory.query.filter_by(a_returned_to_party=True, a_returned_shipped=True).order_by(Inventory.id.desc()).all()),
        ('b', Inventory.query.filter_by(b_returned_to_party=True, b_returned_shipped=True).order_by(Inventory.id.desc()).all()),
    ):
        for inventory in returned_inventories:
            returned_quantity = max(0.0, parse_numeric(getattr(inventory, f'{quality}_returned_quantity', 0)))
            if returned_quantity <= 0:
                continue

            order_ref = Order.query.filter_by(job_no=inventory.order_id).first()
            party_name = getattr(inventory, f'{quality}_returned_party', '') or (order_ref.name if order_ref else inventory.received_from or 'Party')
            article_name = getattr(inventory, f'{quality}_returned_article', '') or (order_ref.article_name if order_ref else inventory.fabric_for or 'Returned fabric')
            job_label = f'RETURNED-{inventory.serial_no or inventory.id}'
            shipment = {
                'id': None,
                'job_no': job_label,
                'shipped_at': getattr(inventory, f'{quality}_returned_date', '') or inventory.recv_date or datetime.utcnow().strftime('%Y-%m-%d'),
                'shipped_by': getattr(inventory, f'{quality}_returned_by', '') or session.get('name') or session.get('user') or 'System',
                'shipped_aq_pcs': 0.0,
                'shipped_bq_pcs': returned_quantity,
                'shipped_pcs': returned_quantity,
                'shipped_packets': 0.0,
                'shipped_ctn': 0.0,
                'shipped_bails': 0.0,
                'ctn_percent': 0.0,
                'bail_percent': 0.0,
            }
            delivered.append({
                'kind': 'inventory_return',
                'return_quality': quality,
                'order': SimpleNamespace(
                    job_no=job_label,
                    name=party_name,
                    article_name=article_name,
                    article_id=order_ref.article_id if order_ref else '',
                    color='',
                    style=(order_ref.style if order_ref else ''),
                    delivered_at=shipment['shipped_at'],
                    delivered_by=shipment['shipped_by'],
                    fulfillment_status='DELIVERED',
                ),
                'shipments': [shipment],
                'total_shipped_pcs': returned_quantity,
            })

    delivered.sort(key=lambda entry: (
        parse_numeric(entry['shipments'][0].get('shipped_pcs', 0)) if isinstance(entry['shipments'][0], dict) else parse_numeric(entry['shipments'][0].shipped_pcs),
        entry['shipments'][0].get('shipped_at', '') if isinstance(entry['shipments'][0], dict) else getattr(entry['shipments'][0], 'shipped_at', ''),
    ), reverse=True)

    db.session.commit()
    return render_template('goods_delivery.html', delivered=delivered)


def get_latest_costing_rates(article_ids):
    article_ids = {article_id for article_id in article_ids if article_id}
    if not article_ids:
        return {}

    rates = {}
    records = CostingSheetHistory.query.filter(
        CostingSheetHistory.article_id.in_(article_ids)
    ).order_by(CostingSheetHistory.created_at.desc(), CostingSheetHistory.id.desc()).all()
    for record in records:
        if record.article_id in rates:
            continue
        try:
            snapshot = json.loads(record.snapshot_json or '{}')
            raw_rate = snapshot.get('totals', {}).get('revised_total')
            if raw_rate is None or not str(raw_rate).strip():
                continue
            rate = float(str(raw_rate).replace(',', '').strip())
            if math.isfinite(rate) and rate >= 0:
                rates[record.article_id] = round(rate, 2)
        except (TypeError, ValueError, json.JSONDecodeError):
            continue
    return rates


def get_billing_lines_for_challan(challan):
    try:
        shipment_ids = [int(value) for value in json.loads(challan.combined_shipment_ids or '[]')]
    except (TypeError, ValueError):
        shipment_ids = []
    if not shipment_ids and challan.shipment_id:
        shipment_ids = [challan.shipment_id]

    shipments_by_id = {
        shipment.id: shipment
        for shipment in ShipmentRecord.query.filter(ShipmentRecord.id.in_(shipment_ids)).all()
    } if shipment_ids else {}
    lines = []
    for shipment_id in shipment_ids:
        shipment = shipments_by_id.get(shipment_id)
        if not shipment:
            continue
        order = db.session.get(Order, shipment.order_id)
        if not order:
            continue
        quantity = parse_numeric(shipment.shipped_aq_pcs) + parse_numeric(shipment.shipped_bq_pcs)
        if quantity <= 0:
            quantity = parse_numeric(shipment.shipped_pcs)
        if quantity <= 0:
            continue
        article = order.article_name or order.article or 'Goods'
        description = ' - '.join(value for value in (article, order.style or '', order.color or '') if value)
        lines.append({
            'key': str(shipment.id),
            'shipment_id': shipment.id,
            'article_id': order.article_id,
            'job_no': shipment.job_no or order.job_no or '',
            'article': article,
            'description': description,
            'quantity': quantity,
            'unit': 'PCS',
        })

    if lines:
        return lines
    if challan.source_type != 'order':
        return []
    order = db.session.get(Order, challan.order_id) if challan.order_id else None
    if not order and challan.job_no:
        order = Order.query.filter_by(job_no=challan.job_no).first()
    quantity = parse_numeric(challan.shipped_pcs)
    if not order or quantity <= 0:
        return []
    article = order.article_name or order.article or challan.article_name or 'Goods'
    description = ' - '.join(value for value in (article, order.style or '', order.color or '') if value)
    return [{
        'key': f'challan-{challan.id}',
        'shipment_id': None,
        'article_id': order.article_id,
        'job_no': order.job_no or challan.job_no or '',
        'article': article,
        'description': description,
        'quantity': quantity,
        'unit': 'PCS',
    }]


def next_billing_number_pair():
    year = datetime.utcnow().year
    invoice_prefix = f'INV-{year}-'
    bill_prefix = f'BILL-{year}-'
    highest = 0
    for value in (
        [invoice.invoice_no for invoice in BillingInvoice.query.filter(BillingInvoice.invoice_no.like(f'{invoice_prefix}%')).all()]
        + [bill.bill_no for bill in CustomerBill.query.filter(CustomerBill.bill_no.like(f'{bill_prefix}%')).all()]
    ):
        try:
            highest = max(highest, int(value.rsplit('-', 1)[-1]))
        except (AttributeError, TypeError, ValueError):
            continue
    sequence = highest + 1
    return f'{invoice_prefix}{sequence:04d}', f'{bill_prefix}{sequence:04d}'


def customer_bill_number_for_invoice(invoice_no):
    parts = (invoice_no or '').split('-')
    if len(parts) == 3 and parts[0] == 'INV' and parts[1].isdigit() and parts[2].isdigit():
        return f'BILL-{parts[1]}-{int(parts[2]):04d}'
    return next_billing_number_pair()[1]


def ensure_customer_bills_for_invoices(shipper):
    invoices = BillingInvoice.query.join(
        ChallanRecord,
        BillingInvoice.challan_id == ChallanRecord.id,
    ).filter(
        func.lower(ChallanRecord.shipped_by_party) == shipper.lower()
    ).all()
    changed = False
    for invoice in invoices:
        bill = CustomerBill.query.filter_by(challan_id=invoice.challan_id).first()
        if not bill:
            bill = CustomerBill(
                bill_no=customer_bill_number_for_invoice(invoice.invoice_no),
                challan_id=invoice.challan_id,
                party_name=invoice.party_name,
                invoice_date=invoice.invoice_date,
                due_date=invoice.due_date,
                currency=invoice.currency,
                subtotal=invoice.subtotal,
                tax_rate=invoice.tax_rate,
                tax_amount=invoice.tax_amount,
                total=invoice.total,
                notes=invoice.notes,
                created_by=invoice.created_by,
                created_at=invoice.created_at,
            )
            db.session.add(bill)
            db.session.flush()
            for challan in invoice.billing_challans:
                db.session.add(CustomerBillChallan(
                    bill_id=bill.id,
                    challan_id=challan.id,
                ))
            for line in invoice.lines:
                db.session.add(CustomerBillLine(
                    bill_id=bill.id,
                    challan_id=line.challan_id or invoice.challan_id,
                    shipment_id=line.shipment_id,
                    job_no=line.job_no,
                    article=line.article,
                    description=line.description,
                    quantity=line.quantity,
                    unit=line.unit,
                    unit_rate=line.unit_rate,
                    amount=line.amount,
                ))
            changed = True

        if not bill.payments and invoice.payments:
            for payment in invoice.payments:
                db.session.add(CustomerBillPayment(
                    bill_id=bill.id,
                    amount=payment.amount,
                    paid_on=payment.paid_on,
                    method=payment.method,
                    reference=payment.reference,
                    notes=payment.notes,
                    received_by=payment.received_by,
                    created_at=payment.created_at,
                ))
            changed = True

    if changed:
        db.session.commit()


def parse_billing_amount(value, label):
    try:
        amount = float(str(value or '0').replace(',', '').strip())
    except (TypeError, ValueError):
        raise ValueError(f'{label} must be a valid number.')
    if not math.isfinite(amount) or amount < 0:
        raise ValueError(f'{label} cannot be negative or invalid.')
    return round(amount, 2)


def normalize_party_ntn(value):
    ntn = (value or '').strip()
    if not ntn:
        return ''
    if ntn.isdigit() and len(ntn) == 8:
        return f'{ntn[:7]}-{ntn[7]}'
    if len(ntn) == 9 and ntn[7] == '-' and ntn[:7].isdigit() and ntn[8].isdigit():
        return ntn
    raise ValueError('NTN must be 8 digits in 7-digit-1-digit format, for example 1234567-8.')


def normalize_sales_tax_no(value):
    sales_tax_no = (value or '').strip()
    if not sales_tax_no:
        return ''
    if sales_tax_no.isdigit() and len(sales_tax_no) == 13:
        return sales_tax_no
    raise ValueError('Sales tax number must contain exactly 13 digits.')


def get_party_record_by_name(party_name):
    if not party_name:
        return None
    normalized = str(party_name).strip()
    if not normalized:
        return None
    return BillingParty.query.filter(func.lower(BillingParty.party_name) == normalized.casefold()).first()


def hydrate_invoice_party_details(invoice):
    if not invoice:
        return None
    party = get_party_record_by_name(invoice.party_name or (invoice.challan.party_name if invoice.challan else ''))
    if not party:
        return invoice
    invoice.party_address = invoice.party_address or (party.address or '')
    invoice.party_city = invoice.party_city or (party.city or '')
    invoice.party_ntn = invoice.party_ntn or (party.ntn or '')
    invoice.sales_tax_no = invoice.sales_tax_no or (party.sales_tax_no or '')
    return invoice


def hydrate_customer_bill_details(bill):
    if not bill:
        return None
    party = get_party_record_by_name(bill.party_name or (bill.challan.party_name if bill.challan else ''))
    if not party:
        return bill
    bill.customer_address = bill.customer_address or (party.address or '')
    bill.customer_phone = bill.customer_phone or (party.phone or '')
    return bill


def build_customer_bill_print_lines(bill_lines, shipment_breakdowns):
    bill_lines_by_shipment = {
        line.shipment_id: line
        for line in bill_lines
        if line.shipment_id
    }
    grouped_lines = {}
    matched_line_ids = set()
    for item in shipment_breakdowns:
        if item.get('quality_pcs') is None:
            continue
        bill_line = bill_lines_by_shipment.get(item.get('shipment_id'))
        if not bill_line:
            bill_line = next((
                line for line in bill_lines
                if line.job_no == item.get('job_no')
                and (not line.article or line.article == item.get('article'))
                and (
                    not item.get('challan_id')
                    or line.challan_id == item.get('challan_id')
                )
            ), None)
        if not bill_line:
            continue
        quality_pcs = parse_numeric(item.get('quality_pcs'))
        if quality_pcs <= 0:
            continue
        article_key = (item.get('article_line') or '').strip().casefold()
        if not article_key:
            continue
        challan_id = bill_line.challan_id or item.get('challan_id')
        key = (challan_id, article_key)
        print_line = grouped_lines.setdefault(key, {
            'note_key': (
                f'article:{article_key}'
                if bill_lines and challan_id == (bill_lines[0].challan_id or item.get('challan_id'))
                else f'article:{challan_id}:{article_key}'
            ),
            'challan_id': challan_id,
            'description': item['article_line'],
            'quantity': 0.0,
            'unit': 'PCS',
            'amount': 0.0,
            'detail_lines': [],
            'unit_notes': [],
        })
        print_line['quantity'] += quality_pcs
        print_line['amount'] += round(quality_pcs * bill_line.unit_rate, 2)
        print_line['detail_lines'].extend(item.get('detail_lines') or [])
        if item.get('unit_note'):
            print_line['unit_notes'].append(item['unit_note'])
        matched_line_ids.add(bill_line.id)

    def prepare_print_line(print_line):
        print_line['quantity'] = round(parse_numeric(print_line['quantity']), 2)
        print_line['quantity_display'] = '{:,.2f}'.format(print_line['quantity']).rstrip('0').rstrip('.')
        print_line['amount'] = round(parse_numeric(print_line['amount']), 2)
        print_line['unit_rate'] = (
            print_line['amount'] / print_line['quantity']
            if print_line['quantity'] else 0.0
        )
        print_line['unit_note'] = ' '.join(dict.fromkeys(print_line.pop('unit_notes', []))) or None
        return print_line

    print_lines = [prepare_print_line(line) for line in grouped_lines.values()]
    print_lines.extend(prepare_print_line({
        'note_key': f'bill-line:{line.id}',
        'challan_id': line.challan_id,
        'description': line.description or line.article,
        'quantity': line.quantity,
        'unit': line.unit,
        'unit_rate': line.unit_rate,
        'amount': line.amount,
    }) for line in bill_lines if line.id not in matched_line_ids)
    return print_lines


def amount_in_words(value, indian=False):
    ones = ('ZERO', 'ONE', 'TWO', 'THREE', 'FOUR', 'FIVE', 'SIX', 'SEVEN', 'EIGHT', 'NINE', 'TEN', 'ELEVEN', 'TWELVE', 'THIRTEEN', 'FOURTEEN', 'FIFTEEN', 'SIXTEEN', 'SEVENTEEN', 'EIGHTEEN', 'NINETEEN')
    tens = ('', '', 'TWENTY', 'THIRTY', 'FORTY', 'FIFTY', 'SIXTY', 'SEVENTY', 'EIGHTY', 'NINETY')
    scales = ('', 'THOUSAND', 'MILLION', 'BILLION', 'TRILLION', 'QUADRILLION', 'QUINTILLION')
    total_paisa = int(round(abs(parse_numeric(value)) * 100))
    rupees, paisa = divmod(total_paisa, 100)

    def below_hundred(number):
        if number < 20:
            return ones[number]
        ten, remainder = divmod(number, 10)
        separator = ' ' if indian else '-'
        return tens[ten] + (f'{separator}{ones[remainder]}' if remainder else '')

    def integer_words(number):
        if number < 100:
            return below_hundred(number)
        hundreds, remainder = divmod(number, 100)
        words = f'{ones[hundreds]} HUNDRED'
        return f'{words} {below_hundred(remainder)}' if remainder else words

    def grouped_integer_words(number):
        if indian:
            groups = []
            number, group = divmod(number, 1000)
            groups.append(group)
            while number:
                number, group = divmod(number, 100)
                groups.append(group)
            scales_indian = ('', 'THOUSAND', 'LAC', 'CRORE', 'ARAB', 'KHARAB', 'NEEL')
            if len(groups) > len(scales_indian):
                raise ValueError('Amount is too large to convert to words.')
            return ' '.join(
                f'{integer_words(group)} {scales_indian[index]}'.strip()
                for index, group in reversed(list(enumerate(groups)))
                if group
            ) or 'ZERO'
        groups = []
        while number:
            number, group = divmod(number, 1000)
            groups.append(group)
        if len(groups) > len(scales):
            raise ValueError('Amount is too large to convert to words.')
        return ', '.join(
            f'{integer_words(group)} {scales[index]}'.strip()
            for index, group in reversed(list(enumerate(groups)))
            if group
        ) or 'ZERO'

    words = grouped_integer_words(rupees)
    if paisa:
        return f'{words} RUPEES AND {integer_words(paisa)} PAISA ONLY'
    return f'{words} RUPEES ONLY'


@app.route('/stock-portal/billing/party-directory', methods=['GET', 'POST'])
def billing_party_directory():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    selected_shipper = normalize_challan_shipper(request.values.get('shipper'))

    if request.method == 'POST':
        action = request.form.get('action', '')
        if action == 'save_party':
            party_id = request.form.get('party_id', type=int)
            party_name = (request.form.get('party_name') or '').strip()
            if not party_name:
                flash('Party name is required.', 'danger')
                return redirect(url_for('billing_party_directory', shipper=selected_shipper))
            party = BillingParty.query.filter_by(id=party_id).first() if party_id else None
            if party_id and not party:
                flash('Select a valid party to update.', 'danger')
                return redirect(url_for('billing_party_directory', shipper=selected_shipper))
            duplicate = BillingParty.query.filter(
                func.lower(BillingParty.party_name) == party_name.casefold(),
                BillingParty.id != (party.id if party else 0),
            ).first()
            if duplicate:
                flash('A party with this name is already saved in the global party directory.', 'danger')
                return redirect(url_for('billing_party_directory', party_id=duplicate.id, shipper=selected_shipper))
            try:
                party_ntn = normalize_party_ntn(request.form.get('party_ntn'))
                sales_tax_no = normalize_sales_tax_no(request.form.get('sales_tax_no'))
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect(url_for('billing_party_directory', shipper=selected_shipper))
            if not party:
                party = BillingParty(shipper=selected_shipper)
            party.party_name = party_name
            party.contact_person = (request.form.get('contact_person') or '').strip()
            party.phone = (request.form.get('party_phone') or '').strip()
            party.email = (request.form.get('party_email') or '').strip()
            party.address = (request.form.get('party_address') or '').strip()
            party.city = (request.form.get('party_city') or '').strip()
            party.ntn = party_ntn
            party.sales_tax_no = sales_tax_no
            party.notes = (request.form.get('party_notes') or '').strip()
            db.session.add(party)
            db.session.commit()
            flash(f'{party.party_name} saved in the global party directory.', 'success')
            return redirect(url_for('billing_party_directory', party_id=party.id, shipper=selected_shipper))
        flash('Choose a valid party directory action.', 'danger')
        return redirect(url_for('billing_party_directory', shipper=selected_shipper))

    party_records = BillingParty.query.order_by(func.lower(BillingParty.party_name)).all()
    party_name_options = sorted({
        (party_name or '').strip()
        for (party_name,) in db.session.query(Article.party_name)
        .filter(Article.party_name.isnot(None), Article.party_name != '')
        .distinct()
        .all()
        if party_name and party_name.strip()
    })
    party_name_options.extend(sorted({
        party.party_name.strip()
        for party in party_records
        if party.party_name and party.party_name.strip()
    }))
    party_name_options = sorted(set(party_name_options))
    selected_party_id = request.args.get('party_id', type=int)
    selected_party = next((party for party in party_records if party.id == selected_party_id), None)
    return render_template(
        'billing_party_directory.html',
        party_records=party_records,
        party_name_options=party_name_options,
        selected_party=selected_party,
        selected_shipper=selected_shipper,
    )


@app.route('/stock-portal/billing', methods=['GET', 'POST'])
def billing_portal():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    selected_shipper = normalize_challan_shipper(request.values.get('shipper'))
    show_billing_notification_cards = (
        request.method == 'GET'
        and not session.get('billing_notification_cards_seen', False)
    )
    if request.method == 'GET':
        session['billing_notification_cards_seen'] = True
    ensure_customer_bills_for_invoices(selected_shipper)

    if request.method == 'POST':
        action = request.form.get('action', '')
        if action == 'save_party':
            party_id = request.form.get('party_id', type=int)
            party_name = (request.form.get('party_name') or '').strip()
            if not party_name:
                flash('Party name is required.', 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))
            party = BillingParty.query.filter_by(id=party_id).first() if party_id else None
            if party_id and not party:
                flash('Select a valid party to update.', 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))
            duplicate = BillingParty.query.filter(
                func.lower(BillingParty.party_name) == party_name.casefold(),
                BillingParty.id != (party.id if party else 0),
            ).first()
            if duplicate:
                flash('A party with this name is already saved in the global party directory.', 'danger')
                return redirect(url_for('billing_portal', party_id=duplicate.id, shipper=selected_shipper))
            try:
                party_ntn = normalize_party_ntn(request.form.get('party_ntn'))
                sales_tax_no = normalize_sales_tax_no(request.form.get('sales_tax_no'))
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))
            if not party:
                party = BillingParty(shipper=selected_shipper)
            party.party_name = party_name
            party.contact_person = (request.form.get('contact_person') or '').strip()
            party.phone = (request.form.get('party_phone') or '').strip()
            party.email = (request.form.get('party_email') or '').strip()
            party.address = (request.form.get('party_address') or '').strip()
            party.city = (request.form.get('party_city') or '').strip()
            party.ntn = party_ntn
            party.sales_tax_no = sales_tax_no
            party.notes = (request.form.get('party_notes') or '').strip()
            db.session.add(party)
            db.session.commit()
            flash(f'{party.party_name} saved in the global party directory.', 'success')
            return redirect(url_for('billing_portal', party_id=party.id, shipper=selected_shipper))

        if action == 'create_invoice':
            challan_ids = list(dict.fromkeys(request.form.getlist('challan_ids', type=int)))
            challans = ChallanRecord.query.filter(
                ChallanRecord.id.in_(challan_ids),
                ChallanRecord.source_type == 'order',
                func.lower(ChallanRecord.shipped_by_party) == selected_shipper.lower(),
            ).order_by(ChallanRecord.id).all() if challan_ids else []
            if not challans or len(challans) != len(challan_ids):
                flash('Select valid delivery challans from this billing portal.', 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))
            party_name = (challans[0].party_name or '').strip()
            if any((challan.party_name or '').strip().casefold() != party_name.casefold() for challan in challans):
                flash('A Bill and Sales Invoice can include challans for only one customer.', 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))

            already_invoiced = {
                challan_id for (challan_id,) in db.session.query(
                    BillingInvoiceChallan.challan_id
                ).filter(BillingInvoiceChallan.challan_id.in_(challan_ids)).all()
            }
            already_billed = {
                challan_id for (challan_id,) in db.session.query(
                    CustomerBillChallan.challan_id
                ).filter(CustomerBillChallan.challan_id.in_(challan_ids)).all()
            }
            for challan in challans:
                if (
                    challan.id in already_invoiced
                    or challan.id in already_billed
                    or BillingInvoice.query.filter_by(challan_id=challan.id).first()
                    or CustomerBill.query.filter_by(challan_id=challan.id).first()
                ):
                    flash(f'Delivery challan {challan.challan_no} has already been billed.', 'danger')
                    return redirect(url_for('billing_portal', shipper=selected_shipper))

            challan_lines = [
                (challan, get_billing_lines_for_challan(challan))
                for challan in challans
            ]
            if any(not lines for _, lines in challan_lines):
                flash('Every selected challan must have billable shipped PCS.', 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))
            costing_rates = get_latest_costing_rates(
                line.get('article_id')
                for _, lines in challan_lines
                for line in lines
            )

            try:
                party = BillingParty.query.filter(
                    func.lower(BillingParty.party_name) == party_name.casefold()
                ).first()
                customer_address = (party.address if party else '').strip()
                customer_phone = (party.phone if party else '').strip()
                invoice_party_address = (party.address if party else '').strip()
                invoice_party_city = (party.city if party else '').strip()
                invoice_party_ntn = (party.ntn if party else '').strip()
                invoice_sales_tax_no = (party.sales_tax_no if party else '').strip()
                invoice_date = request.form.get('invoice_date') or datetime.utcnow().strftime('%Y-%m-%d')
                datetime.strptime(invoice_date, '%Y-%m-%d')
                due_date = (request.form.get('due_date') or '').strip()
                if due_date:
                    datetime.strptime(due_date, '%Y-%m-%d')
                tax_rate = parse_billing_amount(request.form.get('tax_rate'), 'Tax rate')
                if tax_rate > 100:
                    raise ValueError('Tax rate cannot exceed 100%.')
                further_tax_rate = parse_billing_amount(request.form.get('further_tax_rate'), 'Further tax rate')
                if further_tax_rate > 100:
                    raise ValueError('Further tax rate cannot exceed 100%.')
                if invoice_party_ntn:
                    further_tax_rate = 0.0
                priced_lines = []
                subtotal = 0.0
                for challan, lines in challan_lines:
                    for line in lines:
                        rate_value = request.form.get(f"unit_rate_{challan.id}_{line['key']}")
                        if rate_value is None or not rate_value.strip():
                            rate_value = costing_rates.get(line.get('article_id'), 0)
                        rate = parse_billing_amount(rate_value, 'Unit rate')
                        amount = round(line['quantity'] * rate, 2)
                        priced_lines.append((challan, line, rate, amount))
                        subtotal += amount
                subtotal = round(subtotal, 2)
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))

            tax_amount = round(subtotal * tax_rate / 100, 2)
            further_tax_amount = round(subtotal * further_tax_rate / 100, 2) if not invoice_party_ntn else 0.0
            invoice_no, bill_no = next_billing_number_pair()
            invoice = BillingInvoice(
                invoice_no=invoice_no,
                challan_id=challans[0].id,
                party_name=party_name,
                party_address=invoice_party_address,
                party_city=invoice_party_city,
                party_ntn=invoice_party_ntn,
                sales_tax_no=invoice_sales_tax_no,
                invoice_date=invoice_date,
                due_date=due_date,
                subtotal=subtotal,
                tax_rate=tax_rate,
                tax_amount=tax_amount,
                further_tax_rate=further_tax_rate,
                further_tax_amount=further_tax_amount,
                total=round(subtotal + tax_amount + further_tax_amount, 2),
                notes=(request.form.get('notes') or '').strip(),
                created_by=session.get('name') or session.get('user') or '',
            )
            bill = CustomerBill(
                bill_no=bill_no,
                challan_id=challans[0].id,
                party_name=party_name,
                customer_address=customer_address,
                customer_phone=customer_phone,
                invoice_date=invoice_date,
                due_date=due_date,
                subtotal=subtotal,
                tax_rate=tax_rate,
                tax_amount=tax_amount,
                further_tax_rate=further_tax_rate,
                further_tax_amount=further_tax_amount,
                total=round(subtotal + tax_amount + further_tax_amount, 2),
                notes=(request.form.get('notes') or '').strip(),
                created_by=session.get('name') or session.get('user') or '',
            )
            try:
                db.session.add_all([invoice, bill])
                db.session.flush()
                for challan in challans:
                    db.session.add(BillingInvoiceChallan(
                        invoice_id=invoice.id,
                        challan_id=challan.id,
                    ))
                    db.session.add(CustomerBillChallan(
                        bill_id=bill.id,
                        challan_id=challan.id,
                    ))
                for challan, line, rate, amount in priced_lines:
                    db.session.add(BillingInvoiceLine(
                        invoice_id=invoice.id,
                        challan_id=challan.id,
                        shipment_id=line['shipment_id'],
                        job_no=line['job_no'],
                        article=line['article'],
                        description=line['description'],
                        quantity=line['quantity'],
                        unit=line['unit'],
                        unit_rate=rate,
                        amount=amount,
                    ))
                    db.session.add(CustomerBillLine(
                        bill_id=bill.id,
                        challan_id=challan.id,
                        shipment_id=line['shipment_id'],
                        job_no=line['job_no'],
                        article=line['article'],
                        description=line['description'],
                        quantity=line['quantity'],
                        unit=line['unit'],
                        unit_rate=rate,
                        amount=amount,
                    ))
                db.session.commit()
            except Exception:
                db.session.rollback()
                app.logger.exception('Unable to create Bill and Sales Invoice')
                flash('Bill and Sales Invoice could not be created. Check whether a selected challan is already billed.', 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))
            flash(f'Bill {bill.bill_no} and Sales Invoice {invoice.invoice_no} created for {len(challans)} challan(s).', 'success')
            return redirect(url_for('billing_portal', invoice_id=invoice.id, shipper=selected_shipper))

        if action == 'record_payment':
            invoice_id = request.form.get('invoice_id', type=int)
            invoice = BillingInvoice.query.get(invoice_id) if invoice_id else None
            if not invoice:
                flash('Invoice not found.', 'danger')
                return redirect(url_for('billing_portal', shipper=selected_shipper))
            if normalize_challan_shipper(invoice.challan.shipped_by_party) != selected_shipper:
                abort(404)
            try:
                amount = parse_billing_amount(request.form.get('amount'), 'Payment amount')
                if amount <= 0:
                    raise ValueError('Payment amount must be greater than zero.')
                paid_on = request.form.get('paid_on') or datetime.utcnow().strftime('%Y-%m-%d')
                datetime.strptime(paid_on, '%Y-%m-%d')
                paid_total = sum(payment.amount for payment in invoice.payments)
                outstanding = round(invoice.total - paid_total, 2)
                if amount > outstanding:
                    raise ValueError(f'Payment cannot exceed the outstanding balance of PKR {outstanding:,.2f}.')
                method = (request.form.get('method') or 'Cash').strip()
                if method not in ('Cash', 'Bank Transfer', 'Cheque', 'Other'):
                    raise ValueError('Select a valid payment method.')
            except ValueError as exc:
                flash(str(exc), 'danger')
                return redirect(url_for('billing_portal', invoice_id=invoice.id, shipper=selected_shipper))
            db.session.add(BillingPayment(
                invoice_id=invoice.id,
                amount=amount,
                paid_on=paid_on,
                method=method,
                reference=(request.form.get('reference') or '').strip(),
                notes=(request.form.get('payment_notes') or '').strip(),
                received_by=session.get('name') or session.get('user') or '',
            ))
            bill = CustomerBill.query.filter_by(challan_id=invoice.challan_id).first()
            if bill:
                db.session.add(CustomerBillPayment(
                    bill_id=bill.id,
                    amount=amount,
                    paid_on=paid_on,
                    method=method,
                    reference=(request.form.get('reference') or '').strip(),
                    notes=(request.form.get('payment_notes') or '').strip(),
                    received_by=session.get('name') or session.get('user') or '',
                ))
            db.session.commit()
            flash(f'Payment of PKR {amount:,.2f} recorded for {invoice.invoice_no}.', 'success')
            return redirect(url_for('billing_portal', invoice_id=invoice.id, shipper=selected_shipper))

        flash('Choose a valid billing action.', 'danger')
        return redirect(url_for('billing_portal', shipper=selected_shipper))

    ensure_shipment_challans()
    invoices = BillingInvoice.query.join(
        ChallanRecord,
        BillingInvoice.challan_id == ChallanRecord.id,
    ).filter(
        func.lower(ChallanRecord.shipped_by_party) == selected_shipper.lower()
    ).order_by(BillingInvoice.created_at.desc(), BillingInvoice.id.desc()).all()
    paid_by_invoice = {
        invoice_id: float(amount or 0)
        for invoice_id, amount in db.session.query(
            BillingPayment.invoice_id,
            func.coalesce(func.sum(BillingPayment.amount), 0),
        ).join(BillingInvoice, BillingPayment.invoice_id == BillingInvoice.id).join(
            ChallanRecord,
            BillingInvoice.challan_id == ChallanRecord.id,
        ).filter(
            func.lower(ChallanRecord.shipped_by_party) == selected_shipper.lower()
        ).group_by(BillingPayment.invoice_id).all()
    }
    today = datetime.utcnow().strftime('%Y-%m-%d')
    party_records = BillingParty.query.order_by(func.lower(BillingParty.party_name)).all()
    party_lookup = {party.party_name.casefold(): party for party in party_records}
    selected_party_id = request.args.get('party_id', type=int)
    selected_party = next((party for party in party_records if party.id == selected_party_id), None)
    invoice_rows = []
    for invoice in invoices:
        paid = round(paid_by_invoice.get(invoice.id, 0.0), 2)
        balance = round(max(invoice.total - paid, 0.0), 2)
        status = 'PAID' if balance <= 0 else 'PARTIAL' if paid > 0 else 'OVERDUE' if invoice.due_date and invoice.due_date < today else 'OPEN'
        invoice_rows.append({'invoice': invoice, 'paid': paid, 'balance': balance, 'status': status})

    search = (request.args.get('q') or '').strip().casefold()
    status_filter = (request.args.get('status') or 'ALL').upper()
    visible_invoice_rows = [
        row for row in invoice_rows
        if (status_filter == 'ALL' or row['status'] == status_filter)
        and (
            not search
            or search in (row['invoice'].invoice_no or '').casefold()
            or search in (row['invoice'].party_name or '').casefold()
            or any(search in (challan.challan_no or '').casefold() for challan in row['invoice'].billing_challans)
            or any(search in (line.job_no or '').casefold() or search in (line.article or '').casefold() for line in row['invoice'].lines)
        )
    ]
    pending_payment_rows = [row for row in invoice_rows if row['balance'] > 0]
    invoiced_challan_ids = {
        challan_id for (challan_id,) in db.session.query(
            BillingInvoiceChallan.challan_id
        ).join(BillingInvoice, BillingInvoiceChallan.invoice_id == BillingInvoice.id).join(
            ChallanRecord, BillingInvoiceChallan.challan_id == ChallanRecord.id
        ).filter(
            func.lower(ChallanRecord.shipped_by_party) == selected_shipper.lower()
        ).all()
    }
    invoiced_challan_ids.update(invoice.challan_id for invoice in invoices)
    billed_challan_ids = {
        challan_id for (challan_id,) in db.session.query(
            CustomerBillChallan.challan_id
        ).join(CustomerBill, CustomerBillChallan.bill_id == CustomerBill.id).join(
            ChallanRecord, CustomerBillChallan.challan_id == ChallanRecord.id
        ).filter(
            func.lower(ChallanRecord.shipped_by_party) == selected_shipper.lower()
        ).all()
    }
    billed_challan_ids.update(
        challan_id for (challan_id,) in db.session.query(
            CustomerBill.challan_id
        ).join(ChallanRecord, CustomerBill.challan_id == ChallanRecord.id).filter(
            func.lower(ChallanRecord.shipped_by_party) == selected_shipper.lower()
        ).all()
    )
    unbilled_challans = ChallanRecord.query.filter(
        ChallanRecord.source_type == 'order',
        func.lower(ChallanRecord.shipped_by_party) == selected_shipper.lower(),
    ).order_by(ChallanRecord.id.desc()).all()
    unbilled_rows = []
    notification_unbilled_count = 0
    notification_unbilled_items = []
    for challan in unbilled_challans:
        if challan.id in invoiced_challan_ids or challan.id in billed_challan_ids:
            continue
        lines = get_billing_lines_for_challan(challan)
        if not lines:
            continue
        notification_unbilled_count += 1
        notification_unbilled_items.append({
            'id': challan.id,
            'challan_no': challan.challan_no,
            'party_name': challan.party_name,
        })
        if search and not any(
            search in (challan.party_name or '').casefold()
            or search in (challan.challan_no or '').casefold()
            or search in (line.job_no or '').casefold()
            or search in (line.article or '').casefold()
            for line in lines
        ):
            continue
        unbilled_rows.append({
            'challan': challan,
            'lines': lines,
            'party': party_lookup.get((challan.party_name or '').casefold()),
        })

    unbilled_party_groups = {}
    for row in unbilled_rows:
        group_key = (row['challan'].party_name or '').strip().casefold()
        group = unbilled_party_groups.setdefault(group_key, {
            'party_name': row['challan'].party_name or 'Customer not specified',
            'rows': [],
        })
        for line in row['lines']:
            line['billing_rate_key'] = f"{row['challan'].id}_{line['key']}"
        group['rows'].append(row)

    costing_rates = get_latest_costing_rates(
        line.get('article_id')
        for row in unbilled_rows
        for line in row['lines']
    )
    for row in unbilled_rows:
        for line in row['lines']:
            line['cost_rate'] = costing_rates.get(line.get('article_id'))

    active_notifications = [
        {
            'notification_type': 'unbilled_challan',
            'reference_key': str(item['id']),
            'title': 'Unbilled delivery challan',
            'message': f"{item['challan_no']} · {item['party_name'] or 'Customer not specified'}",
        }
        for item in notification_unbilled_items
    ]
    active_notifications.extend(
        {
            'notification_type': 'pending_payment',
            'reference_key': str(row['invoice'].id),
            'title': 'Pending invoice payment',
            'message': (
                f"{row['invoice'].invoice_no} · "
                f"{row['invoice'].party_name or 'Customer not specified'} · "
                f"PKR {row['balance']:,.2f} outstanding"
            ),
        }
        for row in pending_payment_rows
    )
    active_notification_keys = {
        (item['notification_type'], item['reference_key'])
        for item in active_notifications
    }
    saved_active_notifications = BillingNotification.query.filter_by(
        shipper=selected_shipper,
        resolved_at=None,
    ).all()
    notifications_changed = False
    for notification in saved_active_notifications:
        key = (notification.notification_type, notification.reference_key)
        if key not in active_notification_keys:
            notification.resolved_at = datetime.utcnow()
            notifications_changed = True
    saved_active_keys = {
        (notification.notification_type, notification.reference_key)
        for notification in saved_active_notifications
        if notification.resolved_at is None
    }
    for item in active_notifications:
        key = (item['notification_type'], item['reference_key'])
        if key in saved_active_keys:
            continue
        db.session.add(BillingNotification(
            shipper=selected_shipper,
            notification_type=item['notification_type'],
            reference_key=item['reference_key'],
            title=item['title'],
            message=item['message'],
        ))
        notifications_changed = True
    if notifications_changed:
        db.session.commit()

    selected_invoice_id = request.args.get('invoice_id', type=int)
    selected_invoice = next((row for row in invoice_rows if row['invoice'].id == selected_invoice_id), None)
    selected_bill = (
        CustomerBill.query.filter_by(challan_id=selected_invoice['invoice'].challan_id).first()
        if selected_invoice else None
    )
    totals = {
        'invoiced': round(sum(invoice.total for invoice in invoices), 2),
        'collected': round(sum(paid_by_invoice.values()), 2),
        'outstanding': round(sum(max(invoice.total - paid_by_invoice.get(invoice.id, 0), 0) for invoice in invoices), 2),
        'unbilled': len(unbilled_rows),
    }
    return render_template(
        'billing.html',
        invoice_rows=visible_invoice_rows,
        unbilled_rows=unbilled_rows,
        unbilled_party_groups=list(unbilled_party_groups.values()),
        selected_invoice=selected_invoice,
        selected_bill=selected_bill,
        party_records=party_records,
        selected_party=selected_party,
        selected_shipper=selected_shipper,
        totals=totals,
        notification_unbilled_count=notification_unbilled_count,
        notification_unbilled_items=notification_unbilled_items[:4],
        pending_payment_count=len(pending_payment_rows),
        pending_payment_total=round(sum(row['balance'] for row in pending_payment_rows), 2),
        pending_payment_items=[{
            'invoice_no': row['invoice'].invoice_no,
            'party_name': row['invoice'].party_name,
            'balance': row['balance'],
        } for row in pending_payment_rows[:4]],
        billing_notification_active_count=BillingNotification.query.filter_by(
            shipper=selected_shipper,
            resolved_at=None,
        ).count(),
        show_billing_notification_cards=show_billing_notification_cards,
        search=request.args.get('q', ''),
        status_filter=status_filter,
        today=today,
    )


@app.route('/stock-portal/billing/notifications')
def billing_notification_history():
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    selected_shipper = normalize_challan_shipper(request.args.get('shipper'))
    notifications = BillingNotification.query.filter_by(
        shipper=selected_shipper
    ).order_by(
        BillingNotification.resolved_at.is_not(None),
        BillingNotification.created_at.desc(),
        BillingNotification.id.desc(),
    ).all()
    return render_template(
        'billing_notification_history.html',
        notifications=notifications,
        selected_shipper=selected_shipper,
        active_count=sum(notification.resolved_at is None for notification in notifications),
    )


@app.route('/stock-portal/billing/<int:invoice_id>/print')
def print_billing_invoice(invoice_id):
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    invoice = BillingInvoice.query.get_or_404(invoice_id)
    hydrate_invoice_party_details(invoice)
    requested_shipper = request.args.get('shipper')
    selected_shipper = normalize_challan_shipper(requested_shipper or invoice.challan.shipped_by_party)
    if requested_shipper and any(
        normalize_challan_shipper(challan.shipped_by_party) != selected_shipper
        for challan in invoice.billing_challans
    ):
        abort(404)
    paid = round(sum(payment.amount for payment in invoice.payments), 2)
    bill = CustomerBill.query.filter_by(challan_id=invoice.challan_id).first()
    hydrate_customer_bill_details(bill)
    return render_template(
        'billing_print.html',
        invoice=invoice,
        bill=bill,
        amount_in_words=amount_in_words(invoice.total),
        paid=paid,
        balance=max(round(invoice.total - paid, 2), 0.0),
        today=datetime.utcnow().strftime('%Y-%m-%d'),
        selected_shipper=selected_shipper,
        company_name='HARAM ENTERPRISES' if selected_shipper == 'Haram' else 'CANON ENTERPRISES',
        company_location='Akhter & Iqbal Compound, Block-C, Ground Floor, L/3, Block-22, F.B. Industrial Area, Opp. Edhi Home, Karachi.',
    )


@app.route('/stock-portal/billing/bill/<int:bill_id>/print', methods=['GET', 'POST'])
def print_billing_bill(bill_id):
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    bill = CustomerBill.query.get_or_404(bill_id)
    hydrate_customer_bill_details(bill)
    requested_shipper = request.args.get('shipper')
    selected_shipper = normalize_challan_shipper(requested_shipper or bill.challan.shipped_by_party)
    bill_challans = bill.billing_challans
    if requested_shipper and any(
        normalize_challan_shipper(challan.shipped_by_party) != selected_shipper
        for challan in bill_challans
    ):
        abort(404)
    sales_invoice = BillingInvoice.query.join(
        BillingInvoiceChallan,
        BillingInvoiceChallan.invoice_id == BillingInvoice.id,
    ).filter(
        BillingInvoiceChallan.challan_id.in_([challan.id for challan in bill_challans])
    ).first()
    hydrate_invoice_party_details(sales_invoice)
    paid = round(sum(payment.amount for payment in bill.payments), 2)
    shipment_breakdowns = []
    for challan in bill_challans:
        challan_breakdowns, _, _ = build_challan_shipment_data(challan)
        for breakdown in challan_breakdowns:
            breakdown['challan_id'] = challan.id
        shipment_breakdowns.extend(challan_breakdowns)
    print_lines = build_customer_bill_print_lines(bill.lines, shipment_breakdowns)
    if request.method == 'POST':
        if request.form.get('action') != 'save_article_note':
            abort(400)
        note_key = (request.form.get('article_key') or '').strip()
        if note_key not in {line['note_key'] for line in print_lines}:
            abort(400)
        note_text = request.form.get('article_note', '')
        if len(note_text) > 500:
            flash('Article notes cannot exceed 500 characters.', 'danger')
            return redirect(url_for('print_billing_bill', bill_id=bill.id, shipper=selected_shipper))

        article_note = CustomerBillArticleNote.query.filter_by(
            bill_id=bill.id,
            article_key=note_key,
        ).first()
        if article_note:
            article_note.note = note_text
        else:
            db.session.add(CustomerBillArticleNote(
                bill_id=bill.id,
                article_key=note_key,
                note=note_text,
            ))
        db.session.commit()
        flash(f'Article note saved for bill {bill.bill_no}.', 'success')
        return redirect(url_for('print_billing_bill', bill_id=bill.id, shipper=selected_shipper))

    saved_notes = {
        note.article_key: note.note
        for note in CustomerBillArticleNote.query.filter_by(bill_id=bill.id).all()
    }
    for line in print_lines:
        line['saved_note'] = saved_notes.get(line['note_key'], '')
    return render_template(
        'customer_bill_print.html',
        bill=bill,
        sales_invoice=sales_invoice,
        paid=paid,
        balance=max(round(bill.total - paid, 2), 0.0),
        today=datetime.utcnow().strftime('%Y-%m-%d'),
        selected_shipper=selected_shipper,
        print_lines=print_lines,
        challans_by_id={challan.id: challan for challan in bill_challans},
        company_name='HARAM ENTERPRISES' if selected_shipper == 'Haram' else 'CANON ENTERPRISES',
        company_logo_screen='haram-black.png' if selected_shipper == 'Haram' else 'canon logo black.webp',
        company_logo_print='haram-black.png' if selected_shipper == 'Haram' else 'canon logo black.webp',
        company_location='Akhter & Iqbal Compound, Block-C, Ground Floor, L/3, Block-22, F.B. Industrial Area, Opp. Edhi Home, Karachi.' if selected_shipper == 'Canon' else '',
        company_phone='36342557' if selected_shipper == 'Canon' else '',
        amount_words=amount_in_words(bill.subtotal),
    )


def is_inventory_return_challan(challan):
    return getattr(challan, 'source_type', '') in ('inventory_return', 'inventory_return_a')


def inventory_return_quality_label(challan):
    return 'A/QUALITY' if getattr(challan, 'source_type', '') == 'inventory_return_a' else 'B/QUALITY'


@app.route('/stock-portal/challan')
def challan_portal():
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    ensure_shipment_challans()
    selected_shipper = (request.args.get('shipper') or 'Canon').strip().title()
    if selected_shipper not in ('Canon', 'Haram'):
        selected_shipper = 'Canon'
    challans = ChallanRecord.query.filter_by(shipped_by_party=selected_shipper).order_by(ChallanRecord.id.desc()).all()
    shipment_summaries = {}
    meter_summaries = {}
    packet_summaries = {}
    direct_pcs_summaries = {}
    for challan in challans:
        shipment_parts = []
        return_meter = parse_numeric(challan.shipped_meter) if is_inventory_return_challan(challan) else 0.0
        explicit_packets = 0.0
        direct_pcs = 0.0
        try:
            shipment_ids = json.loads(challan.combined_shipment_ids or '[]')
        except (TypeError, ValueError):
            shipment_ids = []
        try:
            inventory_ids = json.loads(challan.combined_inventory_ids or '[]')
        except (TypeError, ValueError):
            inventory_ids = []
        if shipment_ids:
            shipments = ShipmentRecord.query.filter(ShipmentRecord.id.in_(shipment_ids)).all()
            shipment_by_id = {shipment.id: shipment for shipment in shipments}
            for shipment_id in shipment_ids:
                shipment = shipment_by_id.get(shipment_id)
                if shipment:
                    shipment_parts.append(shipment.job_no or f'SHIPMENT-{shipment.id}')
                    shipment_order = db.session.get(Order, shipment.order_id)
                    aq_packets = parse_numeric(shipment.shipped_aq_packets)
                    bq_packets = parse_numeric(shipment.shipped_bq_packets)
                    aq_ctn = parse_numeric(shipment.shipped_aq_ctn)
                    bq_ctn = parse_numeric(shipment.shipped_bq_ctn)
                    aq_bails = parse_numeric(shipment.shipped_aq_bails)
                    bq_bails = parse_numeric(shipment.shipped_bq_bails)
                    shipment_pcs = (
                        parse_numeric(shipment.shipped_aq_pcs)
                        + parse_numeric(shipment.shipped_bq_pcs)
                    )
                    pcs_per_poly = parse_numeric(shipment_order.pcs_poly) if shipment_order else 0.0
                    derived_fractional_packets = 0.0
                    if (
                        pcs_per_poly > 0
                        and aq_ctn + bq_ctn + aq_bails + bq_bails <= 0
                        and aq_packets + bq_packets > 0
                        and abs((aq_packets + bq_packets) * pcs_per_poly - shipment_pcs) < 0.01
                        and not (aq_packets + bq_packets).is_integer()
                    ):
                        derived_fractional_packets = aq_packets + bq_packets
                    explicit_packets += (aq_packets + bq_packets) - derived_fractional_packets
                    shipment_direct_pcs = (
                        parse_numeric(shipment.shipped_aq_direct_pcs)
                        + parse_numeric(shipment.shipped_bq_direct_pcs)
                    )
                    shipment_unit_type = (shipment.shipment_unit_type or '').upper()
                    if shipment_unit_type and 'PACKETS' not in shipment_unit_type:
                        explicit_packets -= (aq_packets + bq_packets) - derived_fractional_packets
                    elif 'PACKETS' in shipment_unit_type:
                        explicit_packets += derived_fractional_packets
                    shipment_packaging_units = (
                        aq_packets + bq_packets + aq_ctn + bq_ctn + aq_bails + bq_bails
                    )
                    if shipment_direct_pcs <= 0 and (
                        shipment_packaging_units <= 0
                        or (derived_fractional_packets > 0 and not shipment_unit_type)
                        or 'PCS' in shipment_unit_type
                    ):
                        shipment_direct_pcs = shipment_pcs
                    direct_pcs += shipment_direct_pcs
        elif challan.source_type == 'order' and challan.job_no:
            shipment_parts.append(challan.job_no)
        for inventory_id in inventory_ids:
            inventory = db.session.get(Inventory, inventory_id)
            if inventory:
                shipment_parts.append(f'{inventory.serial_no or f"INV-{inventory.id}"} FABRIC RETURN')
                return_meter += parse_numeric(inventory.b_returned_quantity)
        if is_inventory_return_challan(challan):
            if challan.inventory_id:
                inventory = db.session.get(Inventory, challan.inventory_id)
                serial_label = inventory.serial_no if inventory else f'INV-{challan.inventory_id}'
                shipment_parts.append(f'{serial_label} {inventory_return_quality_label(challan)} FABRIC RETURN')
            elif not shipment_parts:
                shipment_parts.append(f'SENT TO PARTY - {inventory_return_quality_label(challan)} FABRIC RETURN')
        shipment_summaries[challan.id] = ', '.join(shipment_parts) or '-'
        meter_summaries[challan.id] = return_meter
        packet_summaries[challan.id] = explicit_packets if shipment_ids else (
            parse_numeric(challan.shipped_aq_packets) + parse_numeric(challan.shipped_bq_packets)
        )
        direct_pcs_summaries[challan.id] = direct_pcs if shipment_ids else (
            parse_numeric(challan.shipped_aq_direct_pcs) + parse_numeric(challan.shipped_bq_direct_pcs)
        )
    return render_template(
        'challan.html',
        challans=challans,
        selected_shipper=selected_shipper,
        shipment_summaries=shipment_summaries,
        meter_summaries=meter_summaries,
        packet_summaries=packet_summaries,
        direct_pcs_summaries=direct_pcs_summaries,
    )


def build_challan_shipment_data(challan):
    def format_quantity(value):
        return f'{float(value or 0):,.2f}'.rstrip('0').rstrip('.')

    def shipment_breakdown(shipment, shipment_order):
        pcs_per_poly = parse_numeric(shipment_order.pcs_poly)
        packets_per_ctn = parse_numeric(shipment_order.qty_ctn)
        packets_per_bail = parse_numeric(shipment_order.qty_bail)
        article_name = shipment_order.article_name or shipment_order.article or '-'
        article_line = f'{article_name} - {shipment_order.style or "-"} - {shipment_order.color or "-"}'
        breakdown = []
        for quality, prefix in (('A/Q', 'aq'), ('B/Q', 'bq')):
            quality_pcs = parse_numeric(getattr(shipment, f'shipped_{prefix}_pcs', 0))
            direct_pcs = parse_numeric(getattr(shipment, f'shipped_{prefix}_direct_pcs', 0))
            packets = parse_numeric(getattr(shipment, f'shipped_{prefix}_packets', 0))
            cartons = parse_numeric(getattr(shipment, f'shipped_{prefix}_ctn', 0))
            bails = parse_numeric(getattr(shipment, f'shipped_{prefix}_bails', 0))
            if quality_pcs <= 0:
                continue

            unit_parts = []
            if direct_pcs > 0:
                unit_parts.append(f'{format_quantity(direct_pcs)} PCS')
            if packets > 0:
                unit_parts.append(f'{format_quantity(packets)} PACKETS')
            if cartons > 0:
                unit_parts.append(f'{format_quantity(cartons)} CTN')
            if bails > 0:
                unit_parts.append(f'{format_quantity(bails)} BAILS')
            if not unit_parts:
                unit_parts.append(f'{format_quantity(quality_pcs)} PCS')

            detail_lines = []
            if direct_pcs > 0:
                detail_lines.append({'line': f'{format_quantity(direct_pcs)} PCS', 'quantity': f'{format_quantity(direct_pcs)} PCS'})
            if packets > 0 and pcs_per_poly > 0:
                detail_lines.append({
                    'line': f'{format_quantity(packets)} PACKETS X {format_quantity(pcs_per_poly)} PCS PER POLY = {format_quantity(packets * pcs_per_poly)} PCS',
                    'quantity': f'{format_quantity(packets)} PACKETS',
                })
            if cartons > 0 and packets_per_ctn > 0 and pcs_per_poly > 0:
                carton_packets = cartons * packets_per_ctn
                detail_lines.append({
                    'line': f'{format_quantity(carton_packets)} PKTS X {format_quantity(pcs_per_poly)} PCS PER POLY = {format_quantity(carton_packets * pcs_per_poly)} PCS',
                    'quantity': f'{format_quantity(cartons)} CTNS',
                })
            if bails > 0 and packets_per_bail > 0 and pcs_per_poly > 0:
                bail_packets = bails * packets_per_bail
                detail_lines.append({
                    'line': f'{format_quantity(bail_packets)} PKTS X {format_quantity(pcs_per_poly)} PCS PER POLY = {format_quantity(bail_packets * pcs_per_poly)} PCS',
                    'quantity': f'{format_quantity(bails)} BAILS',
                })
            if not detail_lines and pcs_per_poly > 0:
                detail_lines.append({
                    'line': f'{format_quantity(quality_pcs / pcs_per_poly)} PACKETS X {format_quantity(pcs_per_poly)} PCS PER POLY = {format_quantity(quality_pcs)} PCS',
                    'quantity': f'{format_quantity(quality_pcs / pcs_per_poly)} PACKETS',
                })

            unit_notes = []
            if cartons > 0 and packets_per_ctn > 0:
                unit_notes.append(f'({format_quantity(packets_per_ctn)} PKTS IN A CTN)')
            if bails > 0 and packets_per_bail > 0:
                unit_notes.append(f'({format_quantity(packets_per_bail)} PKTS IN A BAIL)')
            breakdown.append({
                'shipment_id': shipment.id,
                'job_no': shipment_order.job_no,
                'article': shipment_order.article,
                'article_line': f'{article_line} - ({quality})',
                'quality_pcs': quality_pcs,
                'shipment_unit': ' + '.join(unit_parts),
                'detail_lines': detail_lines,
                'unit_note': ' '.join(unit_notes) if unit_notes else None,
            })
        return breakdown

    shipment_breakdowns = []
    combined_items = []
    combined_returns = []
    try:
        combined_shipment_ids = json.loads(challan.combined_shipment_ids or '[]')
    except (TypeError, ValueError):
        combined_shipment_ids = []
    try:
        combined_inventory_ids = json.loads(challan.combined_inventory_ids or '[]')
    except (TypeError, ValueError):
        combined_inventory_ids = []

    if combined_shipment_ids:
        for shipment in ShipmentRecord.query.filter(ShipmentRecord.id.in_(combined_shipment_ids)).all():
            shipment_order = db.session.get(Order, shipment.order_id)
            if not shipment_order:
                continue
            combined_items.append({
                'article_name': shipment_order.article_name or shipment_order.article or '-',
                'style': shipment_order.style or '-',
                'color': shipment_order.color or '-',
                'aq_pcs': parse_numeric(shipment.shipped_aq_pcs),
                'bq_pcs': parse_numeric(shipment.shipped_bq_pcs),
            })
            shipment_breakdowns.extend(shipment_breakdown(shipment, shipment_order))

    for inventory_id in combined_inventory_ids:
        inventory = db.session.get(Inventory, inventory_id)
        if not inventory:
            continue
        article_name = inventory.b_returned_article or inventory.fabric_for or 'Returned Fabric'
        quantity = parse_numeric(inventory.b_returned_quantity)
        combined_items.append({'article_name': article_name, 'style': '-', 'color': '-'})
        combined_returns.append({'article_name': article_name, 'quantity': quantity})
        shipment_breakdowns.append({
            'shipment_id': None,
            'job_no': inventory.order_id,
            'article': article_name,
            'article_line': f'{article_name} - FABRIC RETURN',
            'shipment_unit': f'{format_quantity(quantity)} MTR',
            'detail_lines': [{'line': f'{format_quantity(quantity)} MTR', 'quantity': f'{format_quantity(quantity)} MTR'}],
            'unit_note': 'B/QUALITY FABRIC RETURN',
        })

    order = db.session.get(Order, challan.order_id) if challan.order_id else None
    if not order and challan.job_no and not str(challan.job_no).startswith('RETURNED-'):
        order = Order.query.filter_by(job_no=challan.job_no).first()
    if not order and challan.inventory_id:
        return_inventory = db.session.get(Inventory, challan.inventory_id)
        if return_inventory and return_inventory.order_id:
            order = Order.query.filter_by(job_no=return_inventory.order_id).first()
    if not combined_shipment_ids and order and challan.shipment_id:
        shipment = db.session.get(ShipmentRecord, challan.shipment_id)
        if shipment:
            shipment_breakdowns = shipment_breakdown(shipment, order)

    if not shipment_breakdowns:
        article_name = challan.article_name or (order.article_name or order.article if order else None) or '-'
        article_line = f'{article_name} - {(order.style if order else None) or "-"} - {(order.color if order else None) or "-"}'
        if is_inventory_return_challan(challan):
            quantity = parse_numeric(challan.shipped_meter)
            shipment_breakdowns.append({
                'shipment_id': challan.shipment_id,
                'job_no': challan.job_no or (order.job_no if order else None),
                'article': order.article if order else article_name,
                'article_line': f'{article_line} - FABRIC RETURN',
                'shipment_unit': f'{format_quantity(quantity)} MTR',
                'detail_lines': [{'line': f'{format_quantity(quantity)} MTR', 'quantity': f'{format_quantity(quantity)} MTR'}],
                'unit_note': f'{inventory_return_quality_label(challan)} FABRIC RETURN',
            })
        else:
            for quality, field in (('A/Q', 'shipped_aq_pcs'), ('B/Q', 'shipped_bq_pcs')):
                quantity = parse_numeric(getattr(challan, field, 0))
                if quantity > 0:
                    shipment_breakdowns.append({
                        'shipment_id': challan.shipment_id,
                        'job_no': challan.job_no or (order.job_no if order else None),
                        'article': order.article if order else article_name,
                        'article_line': f'{article_line} - ({quality})',
                        'shipment_unit': f'{format_quantity(quantity)} PCS',
                        'detail_lines': [{'line': f'{format_quantity(quantity)} PCS', 'quantity': f'{format_quantity(quantity)} PCS'}],
                        'unit_note': None,
                    })

    return shipment_breakdowns, combined_items, combined_returns


@app.route('/stock-portal/challan/<int:challan_id>/print')
def print_challan(challan_id):
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    challan = ChallanRecord.query.get_or_404(challan_id)
    customer_bill = (
        CustomerBill.query
        .outerjoin(CustomerBillChallan, CustomerBillChallan.bill_id == CustomerBill.id)
        .filter(or_(
            CustomerBill.challan_id == challan.id,
            CustomerBillChallan.challan_id == challan.id,
        ))
        .order_by(CustomerBill.created_at.desc(), CustomerBill.id.desc())
        .first()
    )
    order = db.session.get(Order, challan.order_id) if challan.order_id else None
    if not order and challan.job_no and not str(challan.job_no).startswith('RETURNED-'):
        order = Order.query.filter_by(job_no=challan.job_no).first()
    if not order and challan.inventory_id:
        return_inventory = db.session.get(Inventory, challan.inventory_id)
        if return_inventory and return_inventory.order_id:
            order = Order.query.filter_by(job_no=return_inventory.order_id).first()

    def format_quantity(value):
        value = float(value or 0)
        return f'{value:,.2f}'.rstrip('0').rstrip('.')

    def shipment_breakdown(shipment, shipment_order):
        pcs_per_poly = parse_numeric(shipment_order.pcs_poly)
        packets_per_ctn = parse_numeric(shipment_order.qty_ctn)
        packets_per_bail = parse_numeric(shipment_order.qty_bail)
        article_name = shipment_order.article_name or shipment_order.article or '-'
        article_line = f'{article_name} - {shipment_order.style or "-"} - {shipment_order.color or "-"}'
        breakdown = []
        for quality, prefix in (('A/Q', 'aq'), ('B/Q', 'bq')):
            quality_pcs = parse_numeric(getattr(shipment, f'shipped_{prefix}_pcs', 0))
            direct_pcs = parse_numeric(getattr(shipment, f'shipped_{prefix}_direct_pcs', 0))
            packets = parse_numeric(getattr(shipment, f'shipped_{prefix}_packets', 0))
            ctn = parse_numeric(getattr(shipment, f'shipped_{prefix}_ctn', 0))
            bails = parse_numeric(getattr(shipment, f'shipped_{prefix}_bails', 0))
            if quality_pcs <= 0:
                continue
            unit_parts = []
            if direct_pcs > 0:
                unit_parts.append(f'{format_quantity(direct_pcs)} PCS')
            if packets > 0:
                unit_parts.append(f'{format_quantity(packets)} PACKETS')
            if ctn > 0:
                unit_parts.append(f'{format_quantity(ctn)} CTN')
            if bails > 0:
                unit_parts.append(f'{format_quantity(bails)} BAILS')
            if not unit_parts:
                unit_parts.append(f'{format_quantity(quality_pcs)} PCS')
            shipment_unit = ' + '.join(unit_parts)
            detail_lines = []
            if direct_pcs > 0:
                detail_lines.append({
                    'line': f'{format_quantity(direct_pcs)} PCS',
                    'quantity': f'{format_quantity(direct_pcs)} PCS',
                })
            if packets > 0 and pcs_per_poly > 0:
                detail_lines.append(
                    {
                        'line': (
                            f'{format_quantity(packets)} PACKETS X '
                            f'{format_quantity(pcs_per_poly)} PCS PER POLY = '
                            f'{format_quantity(packets * pcs_per_poly)} PCS'
                        ),
                        'quantity': f'{format_quantity(packets)} PACKETS',
                    }
                )
            if ctn > 0 and packets_per_ctn > 0 and pcs_per_poly > 0:
                ctn_packets = ctn * packets_per_ctn
                detail_lines.append(
                    {
                        'line': (
                            f'{format_quantity(ctn_packets)} PKTS X '
                            f'{format_quantity(pcs_per_poly)} PCS PER POLY = '
                            f'{format_quantity(ctn_packets * pcs_per_poly)} PCS'
                        ),
                        'quantity': f'{format_quantity(ctn)} CTNS',
                    }
                )
            if bails > 0 and packets_per_bail > 0 and pcs_per_poly > 0:
                bail_packets = bails * packets_per_bail
                detail_lines.append(
                    {
                        'line': (
                            f'{format_quantity(bail_packets)} PKTS X '
                            f'{format_quantity(pcs_per_poly)} PCS PER POLY = '
                            f'{format_quantity(bail_packets * pcs_per_poly)} PCS'
                        ),
                        'quantity': f'{format_quantity(bails)} BAILS',
                    }
                )
            if not detail_lines and pcs_per_poly > 0:
                detail_lines.append(
                    {
                        'line': (
                            f'{format_quantity(quality_pcs / pcs_per_poly)} PACKETS X '
                            f'{format_quantity(pcs_per_poly)} PCS PER POLY = '
                            f'{format_quantity(quality_pcs)} PCS'
                        ),
                        'quantity': f'{format_quantity(quality_pcs / pcs_per_poly)} PACKETS',
                    }
                )
            unit_notes = []
            if ctn > 0 and packets_per_ctn > 0:
                unit_notes.append(f'({format_quantity(packets_per_ctn)} PKTS IN A CTN)')
            if bails > 0 and packets_per_bail > 0:
                unit_notes.append(f'({format_quantity(packets_per_bail)} PKTS IN A BAIL)')
            unit_note = ' '.join(unit_notes) if unit_notes else None
            total_pcs = (
                direct_pcs
                + packets * pcs_per_poly
                + ctn * packets_per_ctn * pcs_per_poly
                + bails * packets_per_bail * pcs_per_poly
            ) or quality_pcs
            breakdown.append({
                'article_line': f'{article_line} - ({quality})',
                'shipment_unit': shipment_unit,
                'detail_lines': detail_lines,
                'unit_note': unit_note,
                'total_pcs': total_pcs,
            })
        return breakdown

    shipment_breakdowns = []
    combined_items = []
    combined_returns = []
    try:
        combined_shipment_ids = json.loads(challan.combined_shipment_ids or '[]')
    except (TypeError, ValueError):
        combined_shipment_ids = []
    try:
        combined_inventory_ids = json.loads(challan.combined_inventory_ids or '[]')
    except (TypeError, ValueError):
        combined_inventory_ids = []
    if combined_shipment_ids:
        for shipment in ShipmentRecord.query.filter(ShipmentRecord.id.in_(combined_shipment_ids)).all():
            shipment_order = db.session.get(Order, shipment.order_id)
            if not shipment_order:
                continue
            combined_items.append({
                'article_name': shipment_order.article_name or shipment_order.article or '-',
                'style': shipment_order.style or '-',
                'color': shipment_order.color or '-',
                'aq_pcs': parse_numeric(shipment.shipped_aq_pcs),
                'bq_pcs': parse_numeric(shipment.shipped_bq_pcs),
            })
            shipment_breakdowns.extend(shipment_breakdown(shipment, shipment_order))
    for inventory_id in combined_inventory_ids:
        inventory = db.session.get(Inventory, inventory_id)
        if not inventory:
            continue
        article_name = inventory.b_returned_article or inventory.fabric_for or 'Returned Fabric'
        combined_items.append({'article_name': article_name, 'style': '-', 'color': '-'})
        combined_returns.append({'article_name': article_name, 'quantity': parse_numeric(inventory.b_returned_quantity)})
        shipment_breakdowns.append({
            'article_line': f'{article_name} - FABRIC RETURN',
            'shipment_unit': f'{format_quantity(inventory.b_returned_quantity)} MTR',
            'packet_line': '',
            'unit_note': 'B/QUALITY FABRIC RETURN',
        })
    if not combined_shipment_ids and order and challan.shipment_id:
        shipment = db.session.get(ShipmentRecord, challan.shipment_id)
        if shipment:
            shipment_breakdowns = shipment_breakdown(shipment, order)
    shipment_total_pcs = sum(item.get('total_pcs', 0) for item in shipment_breakdowns)
    if shipment_total_pcs <= 0:
        shipment_total_pcs = parse_numeric(challan.shipped_pcs)
    print_mode = request.args.get('mode', 'customer')
    shipper = normalize_challan_shipper(challan.shipped_by_party)
    if print_mode == 'canon_customer':
        copy_labels = ['CUSTOMER COPY', f'{shipper.upper()} COPY']
    elif print_mode == 'billing':
        copy_labels = ['FOR BILLING']
    else:
        copy_labels = ['CUSTOMER COPY']
    company_name = 'HARAM ENTERPRISES' if shipper == 'Haram' else 'CANON ENTERPRISES'
    is_combined_shipment = len(combined_shipment_ids) > 1 or bool(combined_inventory_ids)
    return render_template(
        'challan_print.html',
        challan=challan,
        customer_bill=customer_bill,
        display_challan_no=format_challan_number(challan.challan_no),
        challan_logo='haram-black.png' if shipper == 'Haram' else 'canon logo black.webp',
        article_style=(order.style if order else '') or '-',
        article_color=(order.color if order else '') or '-',
        is_inventory_return=is_inventory_return_challan(challan),
        return_quality_label=inventory_return_quality_label(challan),
        combined_items=combined_items,
        combined_returns=combined_returns,
        shipment_breakdowns=shipment_breakdowns,
        shipment_total_pcs=shipment_total_pcs,
        is_combined_shipment=is_combined_shipment,
        copy_labels=copy_labels,
        print_mode=print_mode,
        company_name=company_name,
    )


@app.route('/stock-portal/goods-delivery/<job_no>/print-summary')
def print_order_shipment_summary(job_no):
    if not stock_portal_access_required():
        return redirect(url_for('index'))

    order = Order.query.filter_by(job_no=job_no).first_or_404()
    shipping = get_order_shipping_snapshot(order)
    return render_template(
        'shipment_summary_print.html',
        order=order,
        shipping=shipping,
        summary_title='Shipment Summary',
        now=datetime.utcnow(),
    )


@app.route('/stock-portal/orders/<path:job_no>/set-status', methods=['POST'])
def set_order_fulfillment_status(job_no):
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    order = Order.query.filter_by(job_no=job_no).first()
    if not order:
        flash('Order not found.', 'danger')
        return redirect(request.referrer or url_for('warehouse_portal'))
    new_status = request.form.get('status', 'PENDING')
    if new_status == 'SHIPPED':
        shipped_by_party = (request.form.get('shipped_by_party') or 'Canon').strip().title()
        if shipped_by_party not in ('Canon', 'Haram'):
            shipped_by_party = 'Canon'
        shipping = warehouse_finished_goods_snapshot(
            order, get_order_shipping_snapshot(order)
        )
        pcs_per_packet = parse_numeric(order.pcs_poly)
        has_flexible_units = any(
            field in request.form
            for field in (
                'shipment_aq_pcs', 'shipment_bq_pcs',
                'shipment_aq_packets', 'shipment_bq_packets',
                'shipment_aq_ctn', 'shipment_bq_ctn',
                'shipment_aq_bails', 'shipment_bq_bails',
            )
        )

        def shipment_units(prefix):
            values = {
                'pcs': parse_numeric(request.form.get(f'shipment_{prefix}_pcs')),
                'packets': parse_numeric(request.form.get(f'shipment_{prefix}_packets')),
                'ctn': parse_numeric(request.form.get(f'shipment_{prefix}_ctn')),
                'bails': parse_numeric(request.form.get(f'shipment_{prefix}_bails')),
            }
            if not has_flexible_units:
                values['packets'] = parse_numeric(request.form.get(f'shipment_{prefix}_packets'))
            if any(value < 0 for value in values.values()):
                raise ValueError('Shipment quantities cannot be negative.')
            if values['packets'] > 0 and pcs_per_packet <= 0:
                raise ValueError('PCS per packet must be configured before sending packets.')
            if values['ctn'] > 0 and (pcs_per_packet <= 0 or shipping['packets_per_ctn'] <= 0):
                raise ValueError('Packets per carton and PCS per packet must be configured before sending cartons.')
            if values['bails'] > 0 and (pcs_per_packet <= 0 or shipping['packets_per_bail'] <= 0):
                raise ValueError('Packets per bail and PCS per packet must be configured before sending bails.')
            values['packet_equivalent'] = (
                values['pcs'] / pcs_per_packet if pcs_per_packet > 0 else 0.0
            ) + values['packets'] + (
                values['ctn'] * shipping['packets_per_ctn']
            ) + (
                values['bails'] * shipping['packets_per_bail']
            )
            values['total_pcs'] = (
                values['pcs']
                + values['packets'] * pcs_per_packet
                + values['ctn'] * shipping['packets_per_ctn'] * pcs_per_packet
                + values['bails'] * shipping['packets_per_bail'] * pcs_per_packet
            )
            return values

        try:
            aq_units = shipment_units('aq')
            bq_units = shipment_units('bq')
        except ValueError as exc:
            flash(str(exc), 'danger')
            return redirect(request.referrer or url_for('warehouse_portal'))
        shipment_aq_pcs = aq_units['total_pcs']
        shipment_bq_pcs = bq_units['total_pcs']
        shipment_pcs = shipment_aq_pcs + shipment_bq_pcs
        ctn_percent = 0.0
        bail_percent = 0.0
        if shipment_aq_pcs < 0 or shipment_bq_pcs < 0 or shipment_pcs <= 0:
            flash('Enter at least one A/Q or B/Q shipment quantity.', 'danger')
            return redirect(request.referrer or url_for('warehouse_portal'))
        if shipment_aq_pcs > shipping['dispatchable_aq_pcs'] + 0.000001 or shipment_bq_pcs > shipping['dispatchable_bq_pcs'] + 0.000001:
            flash('Shipment PCS cannot exceed warehouse-located A/Q or B/Q stock.', 'danger')
            return redirect(request.referrer or url_for('warehouse_portal'))
        packets = aq_units['packet_equivalent'] + bq_units['packet_equivalent']
        shipped_ctn = aq_units['ctn'] + bq_units['ctn']
        shipped_bails = aq_units['bails'] + bq_units['bails']
        shipment_unit_type = ','.join(
            unit for unit, value in (
                ('PCS', aq_units['pcs'] + bq_units['pcs']),
                ('PACKETS', aq_units['packets'] + bq_units['packets']),
                ('CTN', shipped_ctn),
                ('BAILS', shipped_bails),
            ) if value > 0
        )
        new_shipped_pcs = shipping['shipped_pcs'] + shipment_pcs
        order.shipped_aq_pcs = f'{shipping["shipped_aq_pcs"] + shipment_aq_pcs:.2f}'
        order.shipped_bq_pcs = f'{shipping["shipped_bq_pcs"] + shipment_bq_pcs:.2f}'
        order.shipped_pcs = f'{new_shipped_pcs:.2f}'
        order.shipped_packets = f'{parse_numeric(order.shipped_packets) + packets:.2f}'
        order.shipped_ctn = f'{parse_numeric(order.shipped_ctn) + shipped_ctn:.2f}'
        order.shipped_bails = f'{parse_numeric(order.shipped_bails) + shipped_bails:.2f}'
        order.fulfillment_status = 'DELIVERED' if new_shipped_pcs >= shipping['completed_pcs'] and shipping['completed_pcs'] > 0 else 'SHIPPED' if new_shipped_pcs > 0 else 'PENDING'
        order.shipped_at = datetime.utcnow().strftime('%Y-%m-%d')
        order.shipped_by = session.get('name') or session.get('user')
        if order.fulfillment_status in ('DELIVERED', 'SHIPPED'):
            order.delivered_at = order.delivered_at or datetime.utcnow().strftime('%Y-%m-%d')
            order.delivered_by = order.delivered_by or session.get('name') or session.get('user')

        shipment_record = ShipmentRecord(
            order_id=order.id,
            job_no=order.job_no,
            shipped_at=datetime.utcnow().strftime('%Y-%m-%d'),
            shipped_by=session.get('name') or session.get('user') or '',
            shipped_aq_pcs=shipment_aq_pcs,
            shipped_bq_pcs=shipment_bq_pcs,
            shipped_aq_direct_pcs=aq_units['pcs'],
            shipped_bq_direct_pcs=bq_units['pcs'],
            shipped_aq_packets=aq_units['packets'],
            shipped_bq_packets=bq_units['packets'],
            shipped_aq_ctn=aq_units['ctn'],
            shipped_bq_ctn=bq_units['ctn'],
            shipped_aq_bails=aq_units['bails'],
            shipped_bq_bails=bq_units['bails'],
            shipped_pcs=shipment_pcs,
            shipped_packets=packets,
            shipped_ctn=shipped_ctn,
            shipped_bails=shipped_bails,
            ctn_percent=ctn_percent,
            bail_percent=bail_percent,
            shipped_by_party=shipped_by_party,
            shipment_unit_type=shipment_unit_type,
        )
        db.session.add(shipment_record)
        try:
            consume_warehouse_finished_goods(
                order.job_no, 'AQ', shipment_aq_pcs, shipment_record
            )
            consume_warehouse_finished_goods(
                order.job_no, 'BQ', shipment_bq_pcs, shipment_record
            )
        except ValueError as exc:
            db.session.rollback()
            flash(str(exc), 'danger')
            return redirect(request.referrer or url_for('warehouse_portal'))
        db.session.commit()
        db.session.add(ChallanRecord(
            challan_no=next_challan_number(shipped_by_party),
            source_type='order',
            shipment_id=shipment_record.id,
            order_id=order.id,
            job_no=order.job_no,
            party_name=order.name or '',
            article_name=order.article_name or order.article or '',
            challan_date=shipment_record.shipped_at,
            shipped_pcs=shipment_pcs,
            shipped_aq_pcs=shipment_aq_pcs,
            shipped_bq_pcs=shipment_bq_pcs,
            shipped_aq_direct_pcs=aq_units['pcs'],
            shipped_bq_direct_pcs=bq_units['pcs'],
            shipped_aq_packets=aq_units['packets'],
            shipped_bq_packets=bq_units['packets'],
            shipped_aq_ctn=aq_units['ctn'],
            shipped_bq_ctn=bq_units['ctn'],
            shipped_aq_bails=aq_units['bails'],
            shipped_bq_bails=bq_units['bails'],
            shipped_packets=packets,
            shipped_ctn=shipped_ctn,
            shipped_bails=shipped_bails,
            shipped_by_party=shipped_by_party,
            created_by=shipment_record.shipped_by or '',
        ))
        db.session.commit()
        flash(f'Shipment marked: {shipment_aq_pcs:.0f} A/Q + {shipment_bq_pcs:.0f} B/Q PCS.', 'success')
        return redirect(url_for('challan_portal', shipper=shipped_by_party))
    order.fulfillment_status = new_status
    who = session.get('name') or session.get('user')
    if new_status == 'SHIPPED':
        order.shipped_at = datetime.utcnow().strftime('%Y-%m-%d')
        order.shipped_by = who
    elif new_status == 'DELIVERED':
        order.delivered_at = datetime.utcnow().strftime('%Y-%m-%d')
        order.delivered_by = who
    db.session.commit()
    flash(f'Order {job_no} status updated to {new_status}.', 'success')
    return redirect(request.referrer or url_for('warehouse_portal'))


@app.route('/stock-portal/warehouse/combined-shipment', methods=['GET', 'POST'])
def create_combined_shipment():
    if not stock_portal_access_required():
        return redirect(url_for('index'))
    if request.method == 'GET':
        job_numbers = request.args.getlist('combined_job_no')
        inventory_ids = request.args.getlist('combined_inventory_id')
        if len(job_numbers) + len(inventory_ids) < 2:
            flash('Select at least two shipment items for a combined shipment.', 'warning')
            return redirect(url_for('warehouse_portal'))
        selected_orders = []
        for job_number in job_numbers:
            order = Order.query.filter_by(job_no=job_number).first()
            if order:
                shipping = warehouse_finished_goods_snapshot(
                    order, get_order_shipping_snapshot(order)
                )
                if shipping['dispatchable_pcs'] > 0.000001:
                    selected_orders.append({'order': order, **shipping})
        selected_returns = [
            inventory for inventory in Inventory.query.filter(Inventory.id.in_(inventory_ids)).all()
            if inventory.b_returned_to_party and not inventory.b_returned_shipped
        ]
        selected_job_set = {str(job_number).strip() for job_number in job_numbers}
        invalid_returns = [
            inventory for inventory in selected_returns
            if not inventory.order_id or str(inventory.order_id).strip() not in selected_job_set
        ]
        if invalid_returns:
            flash('Select the order linked to each returned fabric item before continuing.', 'warning')
            return redirect(url_for('warehouse_portal'))
        if len(selected_orders) + len(selected_returns) < 2:
            flash('At least two valid shipment items are required for a combined shipment.', 'warning')
            return redirect(url_for('warehouse_portal'))
        return render_template('combined_shipment.html', selected_orders=selected_orders, selected_returns=selected_returns)
    job_numbers = request.form.getlist('combined_job_no')
    inventory_ids = request.form.getlist('combined_inventory_id')
    shipped_by_party = (request.form.get('shipped_by_party') or 'Canon').strip().title()
    if shipped_by_party not in ('Canon', 'Haram'):
        shipped_by_party = 'Canon'
    if len(job_numbers) + len(inventory_ids) < 2:
        flash('Select at least two shipment items for a combined shipment.', 'warning')
        return redirect(url_for('warehouse_portal'))

    shipment_records = []
    challan_totals = {
        'shipped_pcs': 0.0, 'shipped_aq_pcs': 0.0, 'shipped_bq_pcs': 0.0,
        'shipped_aq_direct_pcs': 0.0, 'shipped_bq_direct_pcs': 0.0,
        'shipped_aq_packets': 0.0, 'shipped_bq_packets': 0.0,
        'shipped_aq_ctn': 0.0, 'shipped_bq_ctn': 0.0,
        'shipped_aq_bails': 0.0, 'shipped_bq_bails': 0.0,
        'shipped_packets': 0.0, 'shipped_ctn': 0.0, 'shipped_bails': 0.0,
    }
    now = datetime.utcnow().strftime('%Y-%m-%d')
    who = session.get('name') or session.get('user') or ''

    try:
        for index, job_number in enumerate(job_numbers):
            order = Order.query.filter_by(job_no=job_number).first()
            if not order:
                raise ValueError(f'Order {job_number} was not found.')
            shipping = warehouse_finished_goods_snapshot(
                order, get_order_shipping_snapshot(order)
            )
            pcs_per_packet = parse_numeric(order.pcs_poly)
            values = {}
            for quality in ('aq', 'bq'):
                values[quality] = {
                    unit: parse_numeric(request.form.get(f'combined_{quality}_{unit}_{index}'))
                    for unit in ('pcs', 'packets', 'ctn', 'bails')
                }
                if any(value < 0 for value in values[quality].values()):
                    raise ValueError('Shipment quantities cannot be negative.')
                if values[quality]['packets'] > 0 and pcs_per_packet <= 0:
                    raise ValueError(f'PCS per packet is not configured for {job_number}.')
                if values[quality]['ctn'] > 0 and (pcs_per_packet <= 0 or shipping['packets_per_ctn'] <= 0):
                    raise ValueError(f'Carton configuration is incomplete for {job_number}.')
                if values[quality]['bails'] > 0 and (pcs_per_packet <= 0 or shipping['packets_per_bail'] <= 0):
                    raise ValueError(f'Bail configuration is incomplete for {job_number}.')
                values[quality]['total_pcs'] = (
                    values[quality]['pcs']
                    + values[quality]['packets'] * pcs_per_packet
                    + values[quality]['ctn'] * shipping['packets_per_ctn'] * pcs_per_packet
                    + values[quality]['bails'] * shipping['packets_per_bail'] * pcs_per_packet
                )
                values[quality]['packet_equivalent'] = (
                    values[quality]['pcs'] / pcs_per_packet if pcs_per_packet > 0 else 0.0
                ) + values[quality]['packets'] + (
                    values[quality]['ctn'] * shipping['packets_per_ctn']
                ) + (values[quality]['bails'] * shipping['packets_per_bail'])
            aq = values['aq']
            bq = values['bq']
            shipment_pcs = aq['total_pcs'] + bq['total_pcs']
            if shipment_pcs <= 0:
                raise ValueError(f'Enter shipment quantities for {job_number}.')
            if aq['total_pcs'] > shipping['dispatchable_aq_pcs'] + 0.000001 or bq['total_pcs'] > shipping['dispatchable_bq_pcs'] + 0.000001:
                raise ValueError(f'Shipment PCS exceeds warehouse-located stock for {job_number}.')
            packets = aq['packet_equivalent'] + bq['packet_equivalent']
            shipped_ctn = aq['ctn'] + bq['ctn']
            shipped_bails = aq['bails'] + bq['bails']
            shipment_unit_type = ','.join(
                unit for unit, value in (
                    ('PCS', aq['pcs'] + bq['pcs']),
                    ('PACKETS', aq['packets'] + bq['packets']),
                    ('CTN', shipped_ctn),
                    ('BAILS', shipped_bails),
                ) if value > 0
            )
            order.shipped_aq_pcs = f'{shipping["shipped_aq_pcs"] + aq["total_pcs"]:.2f}'
            order.shipped_bq_pcs = f'{shipping["shipped_bq_pcs"] + bq["total_pcs"]:.2f}'
            order.shipped_pcs = f'{shipping["shipped_pcs"] + shipment_pcs:.2f}'
            order.shipped_packets = f'{parse_numeric(order.shipped_packets) + packets:.2f}'
            order.shipped_ctn = f'{parse_numeric(order.shipped_ctn) + shipped_ctn:.2f}'
            order.shipped_bails = f'{parse_numeric(order.shipped_bails) + shipped_bails:.2f}'
            order.shipped_at = now
            order.shipped_by = who
            order.fulfillment_status = 'DELIVERED' if order.shipped_pcs and parse_numeric(order.shipped_pcs) >= shipping['completed_pcs'] else 'SHIPPED'
            shipment = ShipmentRecord(
                order_id=order.id, job_no=order.job_no, shipped_at=now, shipped_by=who,
                shipped_aq_pcs=aq['total_pcs'], shipped_bq_pcs=bq['total_pcs'],
                shipped_aq_direct_pcs=aq['pcs'], shipped_bq_direct_pcs=bq['pcs'],
                shipped_aq_packets=aq['packets'], shipped_bq_packets=bq['packets'],
                shipped_aq_ctn=aq['ctn'], shipped_bq_ctn=bq['ctn'],
                shipped_aq_bails=aq['bails'], shipped_bq_bails=bq['bails'],
                shipped_pcs=shipment_pcs, shipped_packets=packets,
                shipped_ctn=shipped_ctn, shipped_bails=shipped_bails,
                shipped_by_party=shipped_by_party,
                shipment_unit_type=shipment_unit_type,
            )
            db.session.add(shipment)
            consume_warehouse_finished_goods(
                order.job_no, 'AQ', aq['total_pcs'], shipment
            )
            consume_warehouse_finished_goods(
                order.job_no, 'BQ', bq['total_pcs'], shipment
            )
            shipment_records.append((order, shipment))
            for key in challan_totals:
                challan_totals[key] += {
                    'shipped_pcs': shipment_pcs, 'shipped_aq_pcs': aq['total_pcs'], 'shipped_bq_pcs': bq['total_pcs'],
                    'shipped_aq_direct_pcs': aq['pcs'], 'shipped_bq_direct_pcs': bq['pcs'],
                    'shipped_aq_packets': aq['packets'], 'shipped_bq_packets': bq['packets'],
                    'shipped_aq_ctn': aq['ctn'], 'shipped_bq_ctn': bq['ctn'],
                    'shipped_aq_bails': aq['bails'], 'shipped_bq_bails': bq['bails'],
                    'shipped_packets': packets, 'shipped_ctn': shipped_ctn, 'shipped_bails': shipped_bails,
                }[key]
        selected_returns = Inventory.query.filter(Inventory.id.in_(inventory_ids)).all()
        valid_returns = [inventory for inventory in selected_returns if inventory.b_returned_to_party and not inventory.b_returned_shipped]
        if len(valid_returns) != len(inventory_ids):
            raise ValueError('One or more returned fabric records are no longer available.')
        selected_job_set = {str(job_number).strip() for job_number in job_numbers}
        if any(not inventory.order_id or str(inventory.order_id).strip() not in selected_job_set for inventory in valid_returns):
            raise ValueError('Select the order linked to each returned fabric item before submitting.')
        for inventory in valid_returns:
            inventory.b_returned_shipped = True
            inventory.b_returned_shipped_by = shipped_by_party
            inventory.b_returned_shipped_date = now
        db.session.flush()
        shipment_ids = [shipment.id for _, shipment in shipment_records]
        inventory_ids = [inventory.id for inventory in valid_returns]
        first_order = shipment_records[0][0] if shipment_records else None
        first_party = first_order.name if first_order else (valid_returns[0].b_returned_party if valid_returns else '')
        db.session.add(ChallanRecord(
            challan_no=next_challan_number(shipped_by_party), source_type='order',
            shipment_id=shipment_ids[0] if shipment_ids else None, combined_shipment_ids=json.dumps(shipment_ids),
            combined_inventory_ids=json.dumps(inventory_ids),
            order_id=first_order.id if first_order else None, job_no=', '.join(dict.fromkeys(job_numbers)) or ', '.join(f'RETURNED-{item.serial_no or item.id}' for item in valid_returns),
            party_name=first_party or '', article_name='COMBINED SHIPMENT',
            challan_date=now, shipped_by_party=shipped_by_party, created_by=who,
            **challan_totals,
        ))
        db.session.commit()
    except ValueError as exc:
        db.session.rollback()
        flash(str(exc), 'danger')
        return redirect(url_for('warehouse_portal'))
    flash(f'Combined shipment created for {len(shipment_records)} shipment entries.', 'success')
    return redirect(url_for('challan_portal', shipper=shipped_by_party))


@app.route('/stock-portal/orders/<path:job_no>/delete-shipment', methods=['POST'])
def delete_order_shipment(job_no):
    if session.get('role') not in ('owner', 'manager') or is_read_only_profile():
        flash('Only owner and manager can delete shipments.', 'danger')
        return redirect(request.referrer or url_for('goods_delivery_portal'))

    if job_no.startswith('RETURNED-'):
        inventory_serial = job_no.replace('RETURNED-', '', 1)
        inventory = Inventory.query.filter_by(serial_no=inventory_serial).first()
        if inventory:
            restore_quality = (request.form.get('return_quality') or '').strip().lower()
            if restore_quality not in {'a', 'b'}:
                restore_quality = get_inventory_return_quality(inventory)
            a_returned_qty = max(0.0, parse_numeric(getattr(inventory, 'a_returned_quantity', 0)))
            b_returned_qty = max(0.0, parse_numeric(getattr(inventory, 'b_returned_quantity', 0)))

            if restore_quality == 'a':
                returned_qty = a_returned_qty
                current_a = max(0.0, parse_numeric(inventory.fabric_qty_a))
                inventory.fabric_qty_a = f'{current_a + returned_qty:.2f}'
                inventory.a_returned_to_party = False
                inventory.a_returned_quantity = '0.00'
                inventory.a_returned_date = ''
                inventory.a_returned_by = ''
                inventory.a_returned_party = ''
                inventory.a_returned_article = ''
                inventory.a_returned_shipped = False
                inventory.a_returned_shipped_by = ''
                inventory.a_returned_shipped_date = ''
                for row in InventorySecondRow.query.filter_by(inventory_id=inventory.id, idx=4).all():
                    if str(getattr(row, 'shortage', '') or '').strip().upper() == 'RETURNED':
                        row.shortage = ''
                        row.balance = ''
                ChallanRecord.query.filter_by(inventory_id=inventory.id, source_type='inventory_return_a').delete()
            else:
                returned_qty = b_returned_qty
                current_b = max(0.0, parse_numeric(inventory.fabric_qty_b))
                inventory.fabric_qty_b = f'{current_b + returned_qty:.2f}'
                inventory.fabric_b_enabled = parse_numeric(inventory.fabric_qty_b) > 0
                inventory.b_returned_to_party = False
                inventory.b_returned_quantity = '0.00'
                inventory.b_returned_date = ''
                inventory.b_returned_by = ''
                inventory.b_returned_party = ''
                inventory.b_returned_article = ''
                inventory.b_returned_shipped = False
                inventory.b_returned_shipped_by = ''
                inventory.b_returned_shipped_date = ''
                for row in InventorySecondRow.query.filter_by(inventory_id=inventory.id, idx=5).all():
                    if str(getattr(row, 'shortage', '') or '').strip().upper() == 'RETURNED':
                        row.shortage = ''
                        row.balance = ''
                ChallanRecord.query.filter_by(inventory_id=inventory.id, source_type='inventory_return').delete()
            inventory.left_over_fabric = f'{max(0.0, parse_numeric(inventory.fabric_qty_a) + max(0.0, parse_numeric(inventory.fabric_qty_b)) - max(0.0, parse_numeric(inventory.used_fabric)) - max(0.0, parse_numeric(inventory.rejected_fabric))):.2f}'
            db.session.commit()
            flash(f'Returned shipment for inventory {inventory_serial} has been removed.', 'success')
            return redirect(request.referrer or url_for('goods_delivery_portal'))
        flash('Returned inventory item not found.', 'danger')
        return redirect(request.referrer or url_for('goods_delivery_portal'))

    shipment_id = request.form.get('shipment_id')
    order = Order.query.filter_by(job_no=job_no).first()
    if not order:
        flash('Order not found.', 'danger')
        return redirect(request.referrer or url_for('goods_delivery_portal'))

    if shipment_id:
        shipment = ShipmentRecord.query.filter_by(id=shipment_id, order_id=order.id).first()
        if shipment:
            ChallanRecord.query.filter_by(shipment_id=shipment.id, source_type='order').delete()
            for dispatch in shipment.warehouse_dispatches:
                dispatch.location.quantity += dispatch.quantity
            db.session.delete(shipment)
            remaining = ShipmentRecord.query.filter_by(order_id=order.id).all()
            total_shipped_pcs = sum(parse_numeric(s.shipped_pcs) for s in remaining)
            order.shipped_aq_pcs = f'{sum(parse_numeric(s.shipped_aq_pcs) for s in remaining):.2f}'
            order.shipped_bq_pcs = f'{sum(parse_numeric(s.shipped_bq_pcs) for s in remaining):.2f}'
            order.shipped_pcs = f'{total_shipped_pcs:.2f}'
            order.shipped_packets = f'{sum(parse_numeric(s.shipped_packets) for s in remaining):.2f}'
            order.shipped_ctn = f'{sum(parse_numeric(s.shipped_ctn) for s in remaining):.2f}'
            order.shipped_bails = f'{sum(parse_numeric(s.shipped_bails) for s in remaining):.2f}'
            order.fulfillment_status = 'SHIPPED' if total_shipped_pcs > 0 else 'PENDING'
            order.shipped_at = remaining[0].shipped_at if remaining else None
            order.shipped_by = remaining[0].shipped_by if remaining else None
            order.delivered_at = order.delivered_at if total_shipped_pcs > 0 else None
            order.delivered_by = order.delivered_by if total_shipped_pcs > 0 else None
            db.session.commit()
            flash(f'Shipment for {job_no} has been removed.', 'success')
            return redirect(request.referrer or url_for('goods_delivery_portal'))

    order.shipped_aq_pcs = '0'
    order.shipped_bq_pcs = '0'
    order.shipped_pcs = '0'
    order.shipped_packets = '0'
    order.shipped_ctn = '0'
    order.shipped_bails = '0'
    order.fulfillment_status = 'PENDING'
    order.shipped_at = None
    order.shipped_by = None
    order.delivered_at = None
    order.delivered_by = None
    ChallanRecord.query.filter_by(order_id=order.id, source_type='order').delete()
    ShipmentRecord.query.filter_by(order_id=order.id).delete()
    db.session.commit()
    flash(f'Shipment for {job_no} has been deleted.', 'success')
    return redirect(request.referrer or url_for('goods_delivery_portal'))


# app.py ke end mein add karein
if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
    # Isse aapko browser mein error message dikhega (sirf testing ke liye)
