/-
**`main`'s frame within the limit's room** (AArch64), the twin of
`Spike/Lib/LowerX64/MainRoomU.lean`: the user `main`'s frame stays above
the first TCB's limit word's value (the first stack's base plus the
`4096`-byte guard) when the user call is entered below `scc_rt_main`'s
frame of `48` (`bareMC`), that is `frame ≤ 12240`
(`hroomU_ofPlaceOK'`, `Spike/Lib/LowerA64/StartCorrectS.lean`).

The rows give it (`Spike/Lib/LowerA64/MainNeed.lean`): `main`'s row has its
frame at most its need `n` (`needOk1`), and `n ≤ 12240`
(`mainNeedOkA_of_placeOKAt`: `scc_rt_main`'s frame of at least `48`
(`mainThread0_frameA`) plus `n` within its row's need, at most the budget,
at most `12288` by `CfgNeedOkA`).

- `mainFrameU_of_placeOKAt`: `main`'s frame at most `12240`.
-/
import Spike.Lib.LowerA64.MainNeed

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf)

/-- **`main`'s frame within the limit's room from the placement check**:
for an `Accepted1` program `p` lowered to `em` and an output passing
`placeOKAt` at a configuration with `CfgNeedOkA`, a stack-checked function
`f` of the IR at index `fi` named `main` has a frame of at most `12240`
bytes. -/
theorem mainFrameU_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hcfg : CfgNeedOkA pcfg = true) {f : Scc.IR.Func} {fi : Nat}
    (hf : (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx)
    (hname : f.name = Scc.Lower.Names.user "main") (hck : f.checkStack = true) :
    (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame ≤ 12240 := by
  obtain ⟨_, n, _, hle, hn, _⟩ := mainNeedOkA_of_placeOKAt hp hlow h hcfg hf hname hck
  omega

end Spike.Lib.LowerA64
