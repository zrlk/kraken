/-
**The refusal path's obligations at hello's root instance** (AArch64; the
instantiation): `h2Stmt_root`'s `hobl` at `HelloRootBase.toPrem`, from `RefO.refOblH_root` at the
start's labels `L0T`, the arena `arW`, the base's debts, contexts and sizes `ls0T ls`, and `h2`'s side `ms2H`;
then `h2Stmt_root` at `toPrem` with every premise but the level's debts covering `DtW` (`hDt`,
discharged at the root) and the text parsing to hello's program (`hhp`).

- `hobl_I`: `hobl` at `toPrem`: the box fresh (`Fresh2H`'s third conjunct), main's id at its TCB (`Box.hmt_H` at
  `Fresh2H`'s first), the kernel by the base's `hK2`, the exit call an abort site of `ms2H` by `refExH`.
- `h2Stmt_rootI`: `h2Stmt_root` at `toPrem` (`toPrem_X2`, `toPrem_G`, `toPrem_Wc`, `hobl_I`).

No new invariant is introduced here. No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloRefRoot
import Spike.Lib.A64HelloH2Root
import Spike.Lib.A64HelloRootInstW

namespace Spike.Lib.A64.HelloPh.RefO

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.HelloPh (ClH lbl2H HelloRootBase)
open Spike.Lib.A64.HelloPh.RefH (RefOblH)
open Spike.Lib.HelloHMid (slWsH)
open Spike.Lib.WakeLoadT (L0T ls0T)

variable {asm : String} {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AW" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "AT" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

variable {hpw i0 E} (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
  (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
  (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hstat : Λ0.static = fun _ => none)

/-- **`h2Stmt_root`'s `hobl` at `toPrem`** (`refOblH_root` at the base's choices): `hhp` the text `asm` parsing to
hello's program (for `refExH` at `ms2H`'s marks), `hDt` the base's debts covering `DtW`. -/
theorem hobl_I (hhp : textProgram asm = .ok SccCode.helloProg)
    (hDt : ∀ s, Spike.Lib.A64.WakeWf.DtW s → B.Dt s) :
    ∀ l b n l' b' n', Spike.Lib.A64.HelloPh.Fresh2H (B.toPrem hpw i0 E hA13 hpin2 hstat).ar (LB) l b n l' b' n' →
      RefOblH (Ly) (B.toPrem hpw i0 E hA13 hpin2 hstat).F0 ((B.toPrem hpw i0 E hA13 hpin2 hstat).G l b n l' b' n')
        l' b' (slWsH l) n'
        (fun s c fs => (B.toPrem hpw i0 E hA13 hpin2 hstat).W2 l b n l' b' n' s c fs ∧
          (B.toPrem hpw i0 E hA13 hpin2 hstat).X2 l b n l' b' n' s c fs) (TakeCKS (AT) (ClH (Ly)))
        (lbl2H (LB) l b l' b') ((B.toPrem hpw i0 E hA13 hpin2 hstat).ms2 l b n l' b' n') := by
  intro l b n l' b' n' hf
  have hpa : textProgram asm = .ok (Ly).prog := by rw [B.hp]; exact hhp
  exact refOblH_root B.hp B.hlo B.hΛ B.hlab B.hsite hf.2.2.1 (Spike.Lib.A64.HelloPh.Box.hmt_H hpw i0 hf.1) hDt
    (B.hK2 l b n l' b' n' hf) (refExH B.hp B.hlo B.hlab B.hΛ hpa _ _ _ _ _ _ _)

/-- **`h2Stmt_root` at `toPrem`** (`ls0 := ls0T B.ls`): its `hX2`, `hG`, `hWc` by `toPrem_X2`, `toPrem_G`,
`toPrem_Wc`, its `hobl` by `hobl_I`. -/
theorem h2Stmt_rootI (hhp : textProgram asm = .ok SccCode.helloProg)
    (hDt : ∀ s, Spike.Lib.A64.WakeWf.DtW s → B.Dt s) :
    Spike.Lib.HelloPreA.H2StmtH (B.toPrem hpw i0 E hA13 hpin2 hstat).W2 (TakeCKS (AT) (ClH (Ly)))
      (B.toPrem hpw i0 E hA13 hpin2 hstat).ar (LB) (B.toPrem hpw i0 E hA13 hpin2 hstat).ms2 (Ly) (Ly).endPc
      (fun l b n l' b' n' s c =>
        Spike.Lib.HelloHMid.BoxMH (Ly) ((B.toPrem hpw i0 E hA13 hpin2 hstat).msB l b n)
          (B.toPrem hpw i0 E hA13 hpin2 hstat).F0 ((B.toPrem hpw i0 E hA13 hpin2 hstat).G l b n l' b' n') l' b'
          (slWsH l) n' s c ∧ Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab) s)
      (Spike.Lib.HelloH2Inv.inv2H (B.toPrem hpw i0 E hA13 hpin2 hstat).W2 (TakeCKS (AT) (ClH (Ly)))
        (B.toPrem hpw i0 E hA13 hpin2 hstat).ms2 (Ly) (AT) (Ly).endPc (LB) (ls0T B.ls)) :=
  Spike.Lib.A64.HelloPh.H2Root.h2Stmt_root hpw i0 (B.toPrem hpw i0 E hA13 hpin2 hstat)
    (HelloRootBase.toPrem_X2 B hA13 hpin2 hstat) (HelloRootBase.toPrem_G B hA13 hpin2 hstat)
    (HelloRootBase.toPrem_Wc B hA13 hpin2 hstat) (hobl_I B hA13 hpin2 hstat hhp hDt)

end Spike.Lib.A64.HelloPh.RefO

/-- info: 'Spike.Lib.A64.HelloPh.RefO.hobl_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.hobl_I

/-- info: 'Spike.Lib.A64.HelloPh.RefO.h2Stmt_rootI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.h2Stmt_rootI
