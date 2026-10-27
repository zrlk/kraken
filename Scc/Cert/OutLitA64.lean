import Scc.Cert.OutLit
import Scc.Cert.PlaceDataA64

/-!
# AArch64 outputs as literals (`scc --cert`)

The `Lean.ToExpr` instances `scc_lit%` (`Scc/Cert/OutLit.lean`) needs for
`Scc.Cert.PlaceOK.A64.Out`: the placement data (`PlaceData`: the block table
`Rt.A64.OGrp` with its rows and static offsets, the stack need table, the
shape of `scc_rt_main`'s tail, the lowered IR `Scc.IR.Program`). The program is Kraken's `Program`, which has
one already.
-/

deriving instance Lean.ToExpr for Spike.Lib.A64.Flow.SO
deriving instance Lean.ToExpr for Scc.Cert.Rt.A64.OBlk
deriving instance Lean.ToExpr for Scc.Cert.Rt.A64.OGrp
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.A64.MainShape
deriving instance Lean.ToExpr for Scc.IR.Width
deriving instance Lean.ToExpr for Scc.IR.Order
deriving instance Lean.ToExpr for Scc.IR.Fence
deriving instance Lean.ToExpr for Scc.IR.BinOp
deriving instance Lean.ToExpr for Scc.IR.UnOp
deriving instance Lean.ToExpr for Scc.IR.Cond
deriving instance Lean.ToExpr for Scc.IR.RmwOp
deriving instance Lean.ToExpr for Scc.IR.Sys
deriving instance Lean.ToExpr for Scc.IR.AbortKind
deriving instance Lean.ToExpr for Scc.IR.Operand
deriving instance Lean.ToExpr for Scc.IR.Addr
deriving instance Lean.ToExpr for Scc.IR.Inst
deriving instance Lean.ToExpr for Scc.IR.Term
deriving instance Lean.ToExpr for Scc.IR.Block
deriving instance Lean.ToExpr for Scc.IR.Func
deriving instance Lean.ToExpr for Scc.IR.DataInit
deriving instance Lean.ToExpr for Scc.IR.Data
deriving instance Lean.ToExpr for Scc.IR.Growth
deriving instance Lean.ToExpr for Scc.IR.Program
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.A64.PlaceData
-- the functions of the block table's stage per function (`Scc/Cert/OutStageA64.lean`)
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.A64.Data.K
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.A64.Data.It
