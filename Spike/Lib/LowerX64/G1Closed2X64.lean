/-
**The x86-64 compiler theorem from the user functions' segments** (G1.5's
last step): `Closed2StmtH` (`Spike/Lib/LowerX64/G1Closed2Final.lean`) by
`closed2Stmt_x64_tg`, the branch-target check `TgOkBStmt` by
`tgOkB_accepted2` (`Spike/Lib/LowerX64/G1TgOk.lean`) from `UserPartStmt`
(`Spike/Lib/LowerX64/G1TgUserStmt.lean`), proved by `userPartStmt`
(`Spike/Lib/LowerX64/G1TgUser.lean`).

- `tgOkBStmt_of`: `TgOkBStmt` from `UserPartStmt`;
- `closed2Stmt_x64_user`: `Closed2StmtH` from `UserPartStmt`;
- `tgOkBStmt`: `TgOkBStmt`;
- `closed2Stmt_x64_final`: **`Closed2StmtH`**, with no premises.
-/
import Spike.Lib.LowerX64.G1Closed2Final
import Spike.Lib.LowerX64.G1TgOk
import Spike.Lib.LowerX64.G1TgUser

namespace Spike.Lib.LowerX64

set_option autoImplicit false

/-- **The branch-target check on every `Accepted2` program's output, from
the user functions' segments** (`tgOkB_accepted2`). -/
theorem tgOkBStmt_of (HU : UserPartStmt) : TgOkBStmt :=
  tgOkB_accepted2 HU

/-- **The x86-64 compiler theorem from the user functions' segments**
(`closed2Stmt_x64_tg` at `tgOkBStmt_of`). -/
theorem closed2Stmt_x64_user (HU : UserPartStmt) : Closed2StmtH :=
  closed2Stmt_x64_tg (tgOkBStmt_of HU)

/-- **The branch-target check passes on every `Accepted2` program's
output** (`tgOkB_accepted2` at `userPartStmt`). -/
theorem tgOkBStmt : TgOkBStmt := tgOkB_accepted2 userPartStmt

/-- **The x86-64 compiler theorem**: `Closed2Stmt` for every `Accepted2`
program at every configuration whose object layout's header scalar count
starts below bit 22 (`closed2Stmt_x64_tg` at `tgOkBStmt`). -/
theorem closed2Stmt_x64_final : Closed2StmtH := closed2Stmt_x64_tg tgOkBStmt

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.tgOkBStmt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.tgOkBStmt_of

/-- info: 'Spike.Lib.LowerX64.closed2Stmt_x64_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2Stmt_x64_user

/-- info: 'Spike.Lib.LowerX64.tgOkBStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.tgOkBStmt

/-- info: 'Spike.Lib.LowerX64.closed2Stmt_x64_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2Stmt_x64_final
