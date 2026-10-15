# Canon Registry

Canon Registry is a lightweight garment-factory ERP and production-control system for managing customer orders, articles, fabric, cutting, production operations, workers, labor payments, and management reporting in one place.

The application is designed around the day-to-day workflow of a garment manufacturing unit. A customer order is converted into an article and production lot, fabric is received and assigned, cutting is planned and recorded, workers enter production against specific cuts and operations, and managers use the resulting records to calculate labor and prepare payouts. Owners get a separate dashboard for factory-wide visibility.

## Business Overview

Canon Registry supports a garment operation that produces apparel articles for parties or customers. Each order can contain manufacturing and packing information such as:

- Party or customer name
- Article number and article name
- Style and color
- Purchase order number
- File number and cut number
- Order quantity in dozen and pieces
- Finish size and cut size
- Fabric width, usage, required fabric, and margin
- Labels, washing cards, logos, embroidery, printing, barcodes, poly bags, and carton details
- Shipment date and challan number
- Optional order-entry image

The printed receiving challan identifies the business location as **Akhtar & Iqbal Compound, Block-A, Ground Floor, L/3, Block-22, F. B. Industrial Area, Opp. Edhi Home, Karachi**. The application branding uses the name Canon Registry.

## How the Business Works

### 1. Maintain the article master

An article is the reusable product definition used by the factory. It stores the article number, name, party, color, style, pieces per side, and margin. Articles can be searched and reused when creating new orders.

### 2. Create a customer order

A manager creates a merchandising order from the selected article or creates a new article while entering the order. The system records the order quantity in dozen and/or pieces and calculates the total order quantity in pieces. Production and fabric records are linked to the order through its job number.

### 3. Prepare costing and requirement slips

Managers and owners can use the article costing sheet to calculate material, operation, printing, embroidery, overhead, and profit values. Costing snapshots can be saved, reviewed from history, deleted, and printed.

Requirement slips group up to six purchase-order items with supplier, priority, rate, and bill information. Saved slips can be searched, edited, grouped by PO, and printed as Canon or customer copies.

### 4. Receive fabric

A receiving challan records fabric arriving from a supplier or other source. It includes supplier, challan, fabric quality, width, fabric purpose, receiving information, vehicle and delivery details, rolls, and fabric quantities. A serial number is generated using the current year.

The inventory record is then used to track fabric position and movement, including:

- Fabric received in quantities A and B
- Fabric issued for cutting
- Fabric returned or used
- Wastage and balance
- Cut sizes and cut pieces
- Supplier, source, file, and serial references

### 5. Prepare cutting sheets

A cutting sheet belongs to an order and represents a cut or cutting batch. It stores cut number, cut size, cutting quantity, fabric meter calculations, palla and piece calculations, cutter information, inventory serial, issue details, shortage, remarks, and balance information.

A cutting sheet must exist before production entries can be recorded against that cut. Multiple cuts can be created for one order, and the next cut number is generated from the existing cuts.

#### Cutting sheet and inventory relationship

The relationship between the cutting sheet and inventory is one of the central mechanics of this system. The flow is:

1. Fabric is first received into inventory.
   - Every receiving challan creates an `Inventory` record with a unique `serial_no`.
   - That record is linked to an `order_id` and stores the received fabric data such as `fabric_qty_a`, `fabric_qty_b`, `fabric_quality`, `width`, `challan_no`, `recv_date`, and `suppliers`.
   - In effect, the inventory record is the master stock container for a received fabric lot.

2. A cutting sheet is then assigned to that inventory stock.
   - When a manager creates a cutting sheet for an order, the form pulls the order's available inventory records and lets the user select one or more inventory serial numbers.
   - The selected inventory is stored in the cutting sheet field `inventory_serial_no`.
   - The code allows one primary inventory serial and, if needed, a secondary serial to be combined. This lets a cut consume material from more than one fabric batch when a single batch is insufficient.
   - The cutting sheet is therefore not an independent record floating without stock; it is tied to the actual fabric lot(s) that will be used for that cut.

3. The cutting sheet calculates how much fabric is needed for the cut.
   - The cut form calculates meter totals from the cutting grid, quantity, range, palla, and other cut data. Those values are stored in fields such as `total_meter`, `total_palla`, `total_pcs`, `balance_fabric`, and `fabric_issue`.
   - Before saving, the system checks the available opening balance for the linked inventory. It validates that the cut's issued fabric does not exceed the available fabric on the selected inventory serial(s).
   - If there is not enough fabric, the system can ask the user to select a secondary inventory record. This is a direct stock-allocation mechanism: the cut is allowed to draw from more than one inventory source.

4. Once the cutting sheet is saved, the system writes usage into the inventory ledger.
   - The app does not just save the cut summary; it creates `InventoryRow` entries linked to the exact `Inventory` row via `InventoryRow.inventory_id`.
   - Each `InventoryRow` records a cut transaction, using fields like:
     - `date`
     - `sno` (the cutting sheet serial number)
     - `cut_no`
     - `file_no`
     - `cut_size`
     - `cutting_pcs`
     - `fabric_req`
     - `fabric_issue`
     - `fabric_return`
     - `fabric_use`
     - `wastage`
     - `cut_pcs`
     - `balance`
   - This creates a detailed ledger trail showing exactly how much fabric was issued to which cutting sheet, how much was used, and what remained in that stock after the cut.

5. The inventory sheet is then updated from the cutting sheet data.
   - When the inventory record is opened, the system reads all related `InventoryRow` entries for that serial.
   - It replays these rows to calculate the cumulative `fabric_use`, `left_over_fabric`, and `rejected_fabric` values.
   - It also updates the running `balance` field on each inventory row so the ledger reflects the remaining quantity after each cut.
   - In other words, the cutting sheet is the source of the depletion event, while the inventory record is the master stock sheet that accumulates those deductions.

6. The final stock state is derived from received stock minus cut usage.
   - The formula is conceptual, not a single SQL field: inventory received + any reactive/recovered fabric adjustments - fabric used by cutting sheets - rejected fabric = current remaining fabric.
   - This is why the app calculates inventory balances through helper functions such as `calculate_inventory_fabric_balances()` and `calculate_inventory_used_fabric()`: they aggregate the cutting-sheet-issued values back into the inventory summary.

In practical terms, the chain is:

Receiving challan -> `Inventory` record with `serial_no` -> cutting sheet chooses `inventory_serial_no` -> cutting sheet saves `fabric_issue` and usage details -> system creates `InventoryRow` records -> inventory screen recalculates the remaining balance and usage totals.

So the inventory table is the source of raw fabric stock, while the cutting sheet acts as the consumption document, and the inventory rows sit in between as the detailed transaction ledger that connects the two.

#### Rejected fabric, re-activated fabric, and B-quality (fabric B)

The logic in this app is more advanced than a simple “received fabric minus used fabric” calculation because it distinguishes between:

- normal fabric A stock (`fabric_qty_a`)
- optional fabric B stock (`fabric_qty_b`)
- rejected fabric (`rejected_fabric`)
- re-activated or recovered fabric (`rejected_recovered_fabric`)

This matters because the cutting-sheet workflow does not treat all fabric as identical. The actual rules in the code are:

1. Rejected fabric is treated as a loss pool.
   - If a fabric lot contains rejected material, the system stores it in `rejected_fabric`.
   - That rejected quantity is removed from the usable stock pool when calculating current stock, so it is not counted as available for future cuts unless it is explicitly reactivated.

2. Re-activated fabric is not extra stock; it is recovered rejected stock.
   - The field `rejected_recovered_fabric` stores how much of the rejected material has been recovered and made usable again.
   - The calculation in `calculate_inventory_fabric_balances()` explicitly says: “Re-active fabric is a portion of rejected fabric, never an extra quantity.”
   - So the recovered material is not added as a completely separate fabric pool. Instead, it is treated as a portion of the rejected quantity that has become usable again.

3. Fabric B is activated only after a defined cut point.
   - `fabric_b_enabled` turns on the second-quality fabric usage mode.
   - `fabric_b_activation_cut_no` and `fabric_b_activation_order_id` define when the B quantity becomes active for a particular order.
   - `inventory_b_activation_cut()` checks whether the stock is supposed to begin using B-quality material only after a chosen cut number.
   - That means a future cutting sheet does not automatically consume B fabric from the start; it only does so once the cut number reaches the activation point.

4. Future cuts use recovered stock only after the chosen primary inventory is used.
   - The code implements `inventory_b_active_for_cut()` and `calculate_inventory_b_quality_remaining()` to ensure B-quality stock is consumed in a controlled, order-sensitive way.
   - The key rule is that B-quality stock is considered active only when the current cut number crosses the activation threshold.
   - If there is recovered/re-activated fabric, it is only available once the order's selected active inventory is being exhausted and the system is moving into later cuts or later stock availability.
   - In other words, the app does not allow recovered fabric to bypass the normal stock progression. It is consumed after the earlier primary inventory is consumed, at the stage when the system decides this fabric batch has become usable for future cuts.

5. The effective inventory pool is recalculated by order and by cut sequence.
   - `calculate_inventory_used_fabric()` walks all cutting sheets linked to the order and their serials.
   - It sorts sheets by cut number and reallocates fabric to each cut in sequence.
   - It also checks if B-quality became active for that inventory at a given cut, then adds the B quantity into the effective balance only for cuts at or after activation.
   - This is why the system can say: “this inventory serial is still using A stock first, then B stock becomes effective later, and recovered fabric becomes usable only after the normal stock path has been used.”

6. The final inventory balance is derived from a layered formula.
   - The system calculates:
     - total raw fabric = `fabric_qty_a + fabric_qty_b`
     - minus rejected fabric
     - minus re-activated fabric used from the rejected pool
     - minus used fabric from all previous cutting sheets
   - The remaining usable quantity then becomes the current available stock.

So the actual hierarchy is:

- Primary inventory / A stock is used first
- Rejected stock is separated as a rejected pool
- Recovered/re-activated stock is reintroduced back into usable stock only within the allowed limits
- B-quality stock becomes active only after the activation cut number
- Future cuts then consume these active pools in the correct order, not all at once

This is the reason the code keeps both `rejected_fabric` and `rejected_recovered_fabric` separate and does not simply add recovered fabric as free stock. The recovered amount is intentionally controlled and only allowed to be used once the remaining valid normal stock and activation logic permit it.

#### Example: primary inventory + secondary stock + reactivated fabric from another inventory

A realistic example in this system is:

- primary selected inventory = `INV-002`
- secondary selected inventory = `INV-003`
- recovered/re-activated fabric from another lot = `INV-001` with `rejected_recovered_fabric = 500`

The cut process works like this:

1. The cutting sheet chooses the active inventory sources.
   - The cut stores `inventory_serial_no` as the selected serial set, usually with the primary serial first and the secondary serial as the fallback or additional source.
   - The app tries to allocate from the selected primary first, and if needed it uses the secondary inventory as the additional pool.

2. The app calculates the available fabric before saving the cut.
   - It builds a balance table for each selected inventory serial.
   - It also checks whether B-quality has become active and whether there is any reactivated fabric available in the relevant inventory.
   - It does not automatically treat `INV-001` recovered fabric as free extra stock for the current cut.

3. Allocation is performed in order.
   - If `INV-002` has enough fabric, that stock is used first.
   - If `INV-002` is short, the additional requirement is allocated from `INV-003`.
   - The system may also consider the recovered or B-quality portion as part of the allowable remaining stock, but only if the activation and cut-order rules permit it.

4. When the cut is saved, the system writes ledger rows to the relevant inventories.
   - For each selected inventory, the app creates an `InventoryRow` record with:
     - `inventory_id`
     - `sno` = cutting-sheet serial number
     - `cut_no` = cut number
     - `fabric_issue`
     - `fabric_use`
     - `balance`
   - Example allocation:
     - `INV-002`: `fabric_use = 500`
     - `INV-003`: `fabric_use = 200`
   - The corresponding balances become:
     - `INV-002 balance = old_balance - 500`
     - `INV-003 balance = old_balance - 200`

5. The reactivated fabric from `INV-001` is only reflected in the inventory balance calculation, not bypassed as a separate free supply.
   - `INV-001` stores `rejected_recovered_fabric = 500`, but the system calculates whether that recovered quantity is still valid to use.
   - It then subtracts the amount already consumed from this recovered pool and keeps `reactive_remaining` as the remaining recoverable/reusable amount.
   - Only future cuts that satisfy the activation and stock rules can consume what remains.

6. The inventory sheets are updated from the ledger rows.
   - The inventory page reads all `InventoryRow` records for that serial.
   - It aggregates them to produce `used_fabric`, `left_over_fabric`, and the running balance.
   - So the actual stock record is never overwritten by a single cut summary; it is rebuilt from the cut transactions.

In short, the design is:

- selected primary and secondary inventories are used for the immediate cut
- reactivated fabric from a different inventory is tracked separately and released only when the system allows it
- the cut’s numeric consumption is pushed into `InventoryRow`
- the main `Inventory` record is then recalculated from those row-level transactions

That is how the system preserves a clean audit trail: one cut is tied to one or more inventory serials, and the inventory ledger then reflects the actual reduction in stock after the cut.

#### Final implemented inventory-to-cutting-sheet behavior

The following is the complete behavior implemented by the current application. It is the authoritative description of how the two sheets work together.

##### 1. Inventory is the stock source

The inventory sheet starts with the fabric received from the customer through the receiving challan. The received fabric is kept under one inventory serial and is divided into these business quantities:

- `fabric_qty_a`: normal/primary fabric quantity
- `fabric_qty_b`: B-quality fabric quantity, stored when received but not usable until activated
- `receive_cut_pcs`: received cut pieces, which are recorded for reference and are not added to meter stock
- `total`: the received meter total recorded on the inventory sheet

The customer may send A fabric, B fabric, and cut pieces together. The inventory header can therefore show `A + B + cut pieces` in the received total, but the cutting-sheet meter calculations use only the fabric quantities that are currently allowed for cutting. `receive_cut_pcs` is not automatically treated as fabric meters because those pieces are sent back to the customer rather than consumed as meter stock.

##### 2. Rejected and re-active fabric are two states of the same stock

If fabric becomes damaged or defective, its meter quantity is entered as `rejected_fabric`. That amount is removed from usable normal stock.

If part of the rejected fabric is washed, repaired, or otherwise becomes usable again, it is entered as `rejected_recovered_fabric` (shown to users as re-active fabric). Re-active fabric is not new fabric and must never increase the original received quantity. It replaces an equal amount of rejected fabric:

```text
updated rejected fabric = original rejected fabric - re-active fabric
usable balance = normal fabric - updated rejected fabric
```

For example:

```text
Original A fabric       = 25,000
Moved to rejected       =  1,000
Normal usable balance   = 24,000
Moved rejected to re-active = 1,000
Updated rejected        = 0
Re-active fabric        = 1,000
Usable opening balance  = 25,000
```

The result is 25,000, not 26,000. Re-active fabric restores part of the original 25,000; it does not add another 1,000.

##### 3. B fabric is inactive until explicitly enabled

Entering a value in `fabric_qty_b` does not activate it. The inventory checkbox `enable_fabric_b` must be checked and saved. The saved state is `Inventory.fabric_b_enabled`.

While the checkbox is not checked:

- B fabric is excluded from the cutting-sheet opening balance
- B fabric is excluded from the cutting-sheet `Total Fabric MTR`
- B fabric cannot be consumed by a cutting sheet
- B fabric is not included in the remaining usable stock

The cutting sheet therefore shows only A fabric, plus any currently usable re-active portion, while B remains inactive.

##### 4. B activation begins on the next cut

When B is enabled after CUT 1, the application records the activation cut as CUT 2. B is not retroactively available to CUT 1. `fabric_b_activation_cut_no` and `fabric_b_activation_order_id` preserve this boundary.

For every later cut, B remains active until its remaining quantity reaches zero. The checkbox does not need to be enabled again for each cut. If B is already enabled and has been used, the application keeps it enabled so historical B usage is not invalidated.

##### 5. Cutting-sheet opening balance and total meter

The cutting sheet displays two different values:

- `Total Fabric MTR`: the quantity originally available for the selected cutting mode
- `Fabric O/B`: the quantity still available before the current cut

The rules are:

```text
Total Fabric MTR before B activation = A quantity
Total Fabric MTR after B activation  = A quantity + B quantity

Fabric O/B = remaining usable A + remaining usable B, when B is active
                + remaining re-active fabric, counted once
```

Re-active fabric is shown separately on the cutting sheet, for example `INV #1 RE-ACTIVE 1000`, but it is included in the usable opening balance only once. It must not be added a second time on top of the inventory leftover.

If B is inactive, the opening balance does not include B. If B is active but already fully consumed, the `FABRIC B.Q ACTIVE` line is hidden or shows no active quantity, while re-active fabric can still remain available.

##### 6. Consumption order for every cut

The application replays inventory ledger rows in cut-number order. Fabric is consumed in this order:

1. Remaining usable A fabric
2. Remaining B fabric, only when B is active for that cut
3. Remaining re-active fabric

This order is calculated by `calculate_inventory_consumption_state()`. It prevents a later B activation from being applied to earlier cuts and prevents re-active fabric from being consumed while active B stock is still available.

The state tracks these independent values:

- `a_remaining`
- `b_remaining`
- `reactive_remaining`
- cumulative `used_fabric`

The inventory page and cutting sheet both use this state so their values remain consistent.

##### 7. Exact CUT 1 to CUT 4 example

Assume the inventory contains:

```text
A fabric                  = 1,000
Re-active fabric          =   200
B fabric                  =   500
B initially enabled      = No
```

Before CUT 1:

```text
Fabric O/B                = 1,200
```

CUT 1 uses 1,100 meters. The system consumes:

```text
1,000 from A
   100 from re-active
```

After CUT 1:

```text
A remaining               = 0
Re-active remaining       = 100
B remaining               = 500, but inactive
```

The manager then checks and saves `Enable Fabric B.Q for future cuts`. The activation cut becomes CUT 2.

Before CUT 2:

```text
Total Fabric MTR          = 1,000 + 500, where the received A total is used as the base display according to the selected sheet
Fabric O/B                = 600
FABRIC B.Q ACTIVE         = 500
Re-active fabric          = 100
```

CUT 2 uses 500 meters. Because B is active, the 500 meters are consumed from B, not from re-active fabric.

Before CUT 3:

```text
B remaining               = 0
Re-active remaining       = 100
Fabric O/B                = 100
FABRIC B.Q ACTIVE         = not displayed because it is zero
Re-active fabric          = 100
```

The same rule applies to larger real values. If CUT 3 opens with:

```text
Fabric O/B                = 3,000
FABRIC B.Q ACTIVE         = 2,000
Re-active fabric          = 1,000
```

and CUT 3 uses 2,000 meters, all 2,000 are taken from B. CUT 4 then opens with:

```text
Fabric O/B                = 1,000
FABRIC B.Q ACTIVE         = hidden because B remaining is zero
Re-active fabric          = 1,000
```

##### 8. Primary and secondary inventory allocation

A cutting sheet may select:

- one primary inventory serial
- one secondary inventory serial

The primary is allocated first. If the primary opening balance is insufficient, the remaining requirement is allocated from the secondary. Each source receives its own inventory ledger row.

For example, if a cut needs 700 meters:

```text
INV-002 primary balance   = 500
INV-003 secondary balance = 300
```

The saved cut creates:

```text
INV-002 InventoryRow.fabric_use = 500
INV-003 InventoryRow.fabric_use = 200
```

The two inventory balances then decrease independently. A re-active pool from another inventory is not silently added to the selected primary or secondary source. It is only considered through the explicit inventory selection and the applicable re-active fallback rules.

##### 9. Data transfer from cutting sheet to inventory

When a cutting sheet is saved, the application performs these operations:

1. Saves the cutting-sheet header and calculations in `CuttingSheet`.
2. Saves the cutting grid rows in `CuttingSheetRow`.
3. Reads the selected primary and secondary inventory serials.
4. Splits the cut's `total_meter` between the selected inventory sources in order.
5. Creates or replaces the matching `InventoryRow` records.
6. Stores cut details in each inventory row, including:
    - `inventory_id`: the exact inventory record used
    - `sno`: cutting-sheet serial number
    - `cut_no`: cut number
    - `date`: cut date
    - `file_no`: order file number
    - `cut_size`: inventory/cut size
    - `cutting_pcs`: cutting quantity
    - `fabric_req`: calculated fabric requirement
    - `fabric_issue`: fabric issued to cutting
    - `fabric_return`: issue minus actual use
    - `fabric_use`: meters consumed from that inventory
    - `wastage`: recorded wastage
    - `cut_pcs`: cut pieces
    - `balance`: balance after this transaction

When an existing cutting sheet is edited, the old matching inventory rows are removed and recreated from the edited allocation. This prevents duplicate usage. When a cutting sheet is deleted, its related production logs and matching inventory ledger rows are also removed.

##### 10. How the inventory page reflects cutting-sheet data

When the inventory page opens, it loads the inventory record and all its `InventoryRow` entries. It then:

- calculates actual used fabric from the row-level `fabric_use` values
- replays usage in cut-number order
- updates the running ledger balance for each row
- calculates remaining A, B, and re-active quantities
- displays the current `Used Fabric`
- displays the current `Left Over Fabric`
- displays the remaining B-quality balance rather than the original B quantity
- displays rejected and re-active fabric separately

The inventory page's `Left Over Fabric` includes the currently usable re-active amount exactly once. The cutting sheet uses the same calculated state for `Fabric O/B`, so it does not add re-active fabric a second time.

The inventory table's B-quality balance also uses the calculated remaining B quantity. For example, if the original B quantity was 5,000 and cutting sheets have used 3,000 from B, the inventory sheet shows a B balance of 2,000. When all B is consumed, it shows zero rather than falling back to the original 5,000.

##### 11. Print behavior

The inventory screen shows the full checkbox label `Enable Fabric B.Q for future cuts`. In print output, the label is shortened to `B-QUALITY ACTIVE` and is printed only when the inventory checkbox is checked. It is not printed when B is inactive.

The printed date column is slightly wider than the normal screen column so dates remain readable without changing the rest of the print table layout.

### 6. Record production

Production is entered against:

- An order or job number
- A cutting-sheet cut number
- A worker
- An operation such as stitching, checking, folding, or packing
- A production date
- A quantity in pieces

The system prevents an operation's recorded quantity for a cut from exceeding that cut's configured piece limit. Production logs become the source for operation summaries, worker earnings, order progress, and dashboard reporting.

When an entry is saved, the production-entry form keeps the current operation selected while its accumulated pieces are below the cut limit. Once the operation reaches the cut limit, the form advances to the next incomplete operation. After every configured operation for the cut reaches the limit, it advances to the next cut and selects the first operation.

### 7. Configure operation rates

The factory can define general operation rates, such as the rate per piece for stitching, checking, folding, or packing. Rates may be assigned or overridden for individual articles and orders. Rate history is retained with an effective date so historical production can be valued using the rate that applied at that time.

### 8. Calculate worker earnings and payouts

For each production log, labor value is calculated as:

`production pieces x applicable operation rate`

Managers can review worker totals by month, week, half-month, or custom period, optionally filtered by department. Payroll supports separate `wages`, `salaried`, and `per_day` worker groups, advance deductions, paid-period tracking, and printable salary sheets.

### 9. Manage workers, departments, attendance, and advances

Worker records contain identity, contact, employment, designation, supervisor, education, department, salary, emergency details, and profile information. Worker accounts use the assigned worker code and CNIC for login. Departments can be maintained separately.

Attendance supports salaried and per-day workers with daily present/absent/holiday status, overtime, night hours, late hours, early leave, Sunday and Pakistan public-holiday handling, monthly history, yearly summaries, and charts. Worker advances and payments are recorded in a ledger. The outstanding advance is calculated as advances minus payments, never below zero.

### 10. Review summaries and dashboards

Managers can filter production by order, cut, worker, month, week, or custom date range. The summary view groups production by operation, worker, and cut.

Summary operations follow the saved sequence from the selected order's operation-rate list. Summary amounts use the order-level operation rate or override configured for that order, while preserving the existing historical-rate fallback for operations without an order-specific rate.

The owner dashboard provides:

- Order and article counts
- Current-month production pieces
- Current-month labor cost
- Inventory quantity and fabric received
- Outstanding worker advances
- Active workers
- Orders without production logs
- Order-by-order progress and recent logs
- Fabric received, used, and remaining by order
- Recent production activity
- Yearly monthly growth chart with production bars and completed-order line
- Annual factory reports with year selection, saved snapshots, management commentary, archive, and print/PDF output

An order is treated as completed when the highest cumulative operation total reaches the order's required piece quantity. The growth chart uses the current calendar year's January-December months and starts a new yearly view automatically when the year changes.

Sales revenue is not currently recorded, so the owner dashboard shows labor cost and advances but does not calculate a complete profit-and-loss result.

## Annual Factory Reports

Owners can open **Annual Report** directly from the owner dashboard. The feature supports selecting any year with data (and the current calendar year), generating a complete yearly snapshot, saving draft commentary, finalizing the report, browsing the archive, and opening an A4-friendly print view.

Annual reports summarize orders, completion, production, labor cost, workers, advances and payments, parties, articles, operations, cuts, fabric movement, utilization, monthly performance, and year-over-year comparisons. Values are calculated from the existing operational records and historical operation-rate logic. Missing source data is shown as `N/A` or `Not available in current system` rather than fabricated.

After finalization, the report is read-only and its JSON snapshot is preserved in the `annual_report` table. Later changes to orders or production logs do not change the finalized report. Revenue, profit, net profit, margin, ROI, and other complete accounting measures remain unavailable because the current system does not record full sales revenue and business expenses.

## User Roles

### Owner

The owner uses `/owner-dashboard` to monitor factory performance, orders, production, labor cost, inventory, advances, worker activity, and yearly growth. The owner can also manage manager and assistant-manager portal accounts, access costing, and administer annual reports.

### Manager

The manager has access to operational administration, including:

- Articles and customer orders
- Receiving challans
- Inventory
- Cutting sheets
- Production entries and logs
- Operation rates
- Workers
- Worker advances
- Payouts
- Production summaries

### Assistant Manager

The assistant manager can access operational views needed for coordination and production work. Many saved operational and administrative views are read-only for this role, but protection is not consistent across every POST or deletion route; deployment should treat this as a current authorization limitation.

### Worker

Workers use the worker portal to view their production, operation rates, earnings, attendance, advances, and net payable. Worker accounts are connected to worker names so production can be attributed to the correct person. Manager job sheets are a separate manager-facing feature.

## Main Modules

| Module | Purpose |
| --- | --- |
| Portal and login | Select a role-specific portal and authenticate users |
| Article master | Store reusable article, party, style, color, and production defaults |
| Merchandising / orders | Create and maintain customer orders and shipment details |
| Article costing | Calculate and save material, operation, overhead, profit, printing, and embroidery costing snapshots |
| Requirement slips | Create, group, search, edit, and print purchase-order requirement slips |
| Receiving challan | Record incoming fabric and delivery information |
| Inventory | Track fabric position, issue, use, return, wastage, and balance |
| Cutting sheet | Plan and save order cuts and fabric calculations |
| Production entry | Record worker production by operation and cut |
| Production log | View detailed production history |
| Operation rates | Manage general, article-level, and order-level labor rates |
| Worker management | Maintain worker profiles and employment data |
| Department management | Maintain worker departments used by administration and payroll filters |
| Worker advances | Record advances and repayments |
| Payout / payroll | Calculate wages, salaried, and per-day payroll with period selection, deductions, and paid status |
| Summary | Filter and review production by period, worker, order, and cut |
| Worker portal | Let workers review production, earnings, attendance, advances, and net payable |
| Owner dashboard | Monitor factory-wide activity and performance |
| Annual reports | Generate, save, finalize, archive, compare, and print yearly factory reports |
| Worker attendance | Record daily attendance, overtime, night hours, lateness, early leave, holidays, history, and yearly summaries |
| Portal controls | Create, edit, and delete manager and assistant-manager portal accounts |
| Print views | Print receiving challans, requirement slips, salary sheets, worker documents, summaries, inventory, cutting sheets, and other operational records |

## Technology

- Python 3
- Flask
- Flask-SQLAlchemy
- Flask-Migrate
- SQLite for local development
- PostgreSQL when `DATABASE_URL` is configured
- Gunicorn for production serving
- Jinja2 templates
- Tailwind CSS via CDN
- Font Awesome via CDN
- Chart.js via CDN for the owner growth chart

## Project Structure

```text
.
├── app.py                 # Flask application, models, routes, and business logic
├── requirements.txt       # Python dependencies
├── render.yaml            # Render deployment configuration
├── canon.db               # Local SQLite database, created/used locally
├── static/
│   └── uploads/           # Uploaded order and worker images
└── templates/             # Jinja2 pages for portals and operational modules
```

## Local Development

### Prerequisites

- Python 3.10 or newer recommended
- PowerShell on Windows or a Unix-compatible shell
- A virtual environment

### Setup on Windows PowerShell

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
pip install -r requirements.txt
python app.py
```

Open the application at `http://127.0.0.1:5000`.

If the Windows `python` command is unavailable, use the virtual-environment interpreter directly after it has been created:

```powershell
.\.venv\Scripts\python.exe app.py
```

### Setup on macOS or Linux

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python app.py
```

## Deployment on Render

The included `render.yaml` defines a Python web service named `canonregistry`:

```yaml
services:
  - type: web
    name: canonregistry
    env: python
    buildCommand: pip install -r requirements.txt
    startCommand: gunicorn app:app
```

For deployment:

1. Connect the repository to Render.
2. Use the included `render.yaml` configuration.
3. Set a strong `SECRET_KEY` environment variable.
4. Set `DATABASE_URL` to a managed PostgreSQL database for persistent production data.
5. Deploy and verify the login and database-backed workflows.

When `DATABASE_URL` is absent, the application falls back to a local `canon.db` SQLite file. A local filesystem database and uploaded files should not be treated as durable production storage on an ephemeral hosting service.

## Configuration and Security

The application reads these environment variables:

| Variable | Purpose |
| --- | --- |
| `SECRET_KEY` | Flask session signing key |
| `DATABASE_URL` | Optional PostgreSQL connection string; otherwise SQLite is used |

The current source contains development login accounts with simple passwords. Change or replace these credentials before production use, set a strong `SECRET_KEY`, and add a proper password-management or identity system before exposing the application publicly.

The order-details route (`/order/<job_no>`) currently renders without requiring a logged-in session. Treat job numbers and the resulting order details as public unless that route is protected before production deployment.

The application also performs best-effort schema updates at startup to support older databases. For production, database backups and a controlled migration process are recommended.

## Data Relationships

```text
Article
  └── Orders
        ├── Receiving Challans
        ├── Inventory Records
        ├── Cutting Sheets
        │     └── Cutting Sheet Rows
        └── Production Logs
              ├── Worker
              └── Operation Rate / Rate History

Worker
  ├── Education Records
  └── Advance and Payment Ledger
```

## Operational Rules

- A production entry is associated with an order and cut number.
- A cutting sheet is required before production can be entered through the production-entry screen.
- Production for an operation and cut cannot exceed the cut's configured quantity.
- Production-entry navigation advances only after the current operation reaches the cut PCS limit; it advances to the next cut only after all configured operations for the current cut are complete.
- Deleting a cutting sheet also deletes production logs matching that sheet's order and cut number.
- The summary uses the operation sequence and configured rates saved for the selected order.
- Order quantity is resolved from pieces first, then dozen converted to pieces, then the legacy quantity field.
- Order production progress uses the highest operation total for that order, avoiding double-counting the same pieces across operations.
- Labor uses the rate effective for the production date when rate history is available.
- Assistant-manager restrictions are partial in the current implementation; some creation and deletion POST routes do not enforce the intended read-only policy.
- Dates are accepted in common formats and displayed as `DD/MM/YYYY` in the interface.
- Running `python app.py` binds the development server to `0.0.0.0:5000`, so it can be reachable from the local network unless the host or firewall restricts it.

## Current Limitations

- Revenue and selling-price data are not implemented, so full profit and loss is unavailable.
- Authentication uses application-defined accounts rather than a full user-management system.
- Portal account administration is limited to manager and assistant-manager accounts; worker access is based on worker code and CNIC.
- The application has no automated test suite in the repository.
- Uploaded files are stored on the local filesystem.
- The order-details page is currently unauthenticated.
- Schema updates are currently handled with startup compatibility logic rather than a fully managed migration workflow.
- Dashboard and reporting calculations load records into Python, which may need optimization as the database grows.

## Business Process at a Glance

```text
Article master
    -> Customer order
    -> Costing and requirement slip
        -> Fabric receiving
            -> Inventory position
                -> Cutting sheet and cut quantity
                    -> Worker production by operation
                        -> Labor calculation
                            -> Advances and payout
                                -> Manager summary and owner dashboard
```

## License

No license file is currently included in the repository. Add a license before distributing the project outside the organization.
