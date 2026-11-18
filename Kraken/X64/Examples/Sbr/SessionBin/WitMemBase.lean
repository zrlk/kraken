import Kraken.X64.Examples.Sbr.SessionBin.Api
import Kraken.X64.Examples.Sbr.Witness

/-!
# Memory witnesses: the addresses and the element's regions

The memories of the witness are built with `Witness.SatIn` (a predicate holds of a memory whose
addresses lie in given intervals; `⋆` of two with disjoint intervals is their union). Each region
is shown satisfiable in one interval (`SatIn.widen`), so the checks of the assembly stay small.

The element sits at `cheW = 0x500000000` (32-aligned); `*sbr` at `sW = cheW + 0x28920`. The whole
allocation is `[cheW, cheW + 0x88ba0)`:
* `[cheW, sW)`: the `ChannelElement` part (`InitGap`);
* `[sW, sW + 0x2b8fc)`: `*sbr`'s scalars, `data[0]`, `data[1]`, `ps->common` (`SbrF`);
* `[sW + 0x2b8fc, sW + 0x4c1e0)`: the rest of `sbr->ps` (`PsRest`);
* `[sW + 0x4c1e0, sW + 0x4c340)`: the frequency tables (`SbrF`'s `TabF`);
* `[sW + 0x4c340, sW + 0x601c0)`: the work arrays (`ArrW`);
* `[sW + 0x601c0, sW + 0x601e0)`, `[sW + 0x60250, sW + 0x60270)`: the transform and routine
  cells (`FnW`); `[sW + 0x601e0, sW + 0x60250)`: `sbr->dsp` (`DspW`);
* `[sW + 0x60270, sW + 0x60280)`: the 16 bytes after `sbr->c` (`InitGap`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init
open Kraken.Examples.Sbr.SessionBin
open Kraken.Examples.Sbr.Witness (SatIn InL DisjL)

namespace Kraken.Examples.Sbr.WitMem

/-! ## The addresses -/

/-- The element (`che`). -/
abbrev cheW : BitVec 64 := 0x500000000#64

/-- `*sbr` (`che + 0x28920`). -/
abbrev sW : BitVec 64 := 0x500028920#64

/-- The decoder context `ac`. -/
abbrev acW : BitVec 64 := 0x200100000#64

/-- `ac->avctx`. -/
abbrev avctxW : BitVec 64 := 0x200700000#64

/-- `ac->fdsp`, the `float_dsp` routine table. -/
abbrev fdspW : BitVec 64 := 0x200200000#64

/-- Init's inputs for the element at the init state: `id_aac = TYPE_SCE`, the `ac` fields above
(extension rate 24000, PS off) and two `av_tx` context addresses. -/
def wI : InitIn where
  idAac := 0
  R := Std.ExtHashMap.emp
  avctx := avctxW
  fdsp := fdspW
  extRate := 24000
  ps := 0
  anaCtx := 0
  synCtx := 0

/-- A memory in the intervals `L` is in any `L'` covering them. -/
theorem SatIn.mono {P : Mem 64 → Prop} {L L' : List (Nat × Nat)} (h : SatIn P L)
    (hL : ∀ n, InL n L → InL n L') : SatIn P L' := by
  obtain ⟨m, hm, hk⟩ := h
  exact ⟨m, hm, fun k hk' => hL _ (hk k hk')⟩

/-- Every interval of `L` lies inside one of `L'` (a Boolean check on numerals). -/
def CovL (L L' : List (Nat × Nat)) : Bool :=
  L.all fun p => L'.any fun q => q.1 ≤ p.1 && p.2 ≤ q.2

theorem CovL_spec {n : Nat} {L L' : List (Nat × Nat)} (h : CovL L L' = true) (hn : InL n L) :
    InL n L' := by
  induction L with
  | nil => exact hn.elim
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    simp only [CovL, List.all_cons, Bool.and_eq_true] at h
    rcases hn with hn | hn
    · obtain ⟨h1, -⟩ := h
      clear ih
      induction L' with
      | nil => simp at h1
      | cons q L' ih2 =>
        obtain ⟨c, d⟩ := q
        simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
        rcases h1 with h1 | h1
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr (ih2 h1)
    · exact ih h.2 hn

theorem SatIn.cover {P : Mem 64 → Prop} {L L' : List (Nat × Nat)} (h : SatIn P L)
    (hc : CovL L L' = true) : SatIn P L' :=
  SatIn.mono h fun _ hn => CovL_spec hc hn

theorem sbrA_tAt : sbrA (tAt cheW acW) = sW := by
  simp only [sbrA, tAt_arg1]; rfl

theorem elemOK_cheW : ElemOK cheW := by
  unfold ElemOK; decide +kernel

/-! ## The element's regions -/

theorem sat_sbrS : SatIn (DecExt.SbrS (toDS (σInit wI)) sW) [(0x500028920, 0x500028920 + 0x80)] := by
  unfold DecExt.SbrS
  exact Witness.SatIn.widen _ _ (by sat_tac) (by decide +kernel)

theorem sat_data0 : SatIn (DecExt.DataF (toDS (σInit wI)).a.d0 (sW + 0x80#64))
    [(0x500028920 + 0x80, 0x500028920 + 0x80 + 0x15ac0)] := by
  unfold DecExt.DataF
  exact Witness.SatIn.widen _ _ (by sat_tac) (by decide +kernel)

theorem sat_data1 : SatIn (DecExt.DataF (toDS (σInit wI)).a.d1 (sW + 0x15b40#64))
    [(0x500028920 + 0x15b40, 0x500028920 + 0x15b40 + 0x15ac0)] := by
  unfold DecExt.DataF
  exact Witness.SatIn.widen _ _ (by sat_tac) (by decide +kernel)

theorem sat_psc : SatIn ((toDS (σInit wI)).a.psc =@ (sW + 0x2b600#64))
    [(0x500028920 + 0x2b600, 0x500028920 + 0x2b600 + 764)] :=
  Witness.SatIn.val (List.length_replicate (n := 764) (a := (0 : UInt8))) (by decide +kernel)

theorem sat_tabF : SatIn (DecExt.TabF (toDS (σInit wI)).a sW)
    [(0x500028920 + 0x4c1e0, 0x500028920 + 0x4c340)] := by
  unfold DecExt.TabF
  exact Witness.SatIn.widen _ _ (by sat_tac) (by decide +kernel)

theorem sat_sbrF : SatIn (DecExt.SbrF (toDS (σInit wI)) sW)
    [(0x500028920, 0x500028920 + 0x2b8fc), (0x500028920 + 0x4c1e0, 0x500028920 + 0x4c340)] := by
  unfold DecExt.SbrF
  exact SatIn.cover (Witness.SatIn.sep sat_sbrS (Witness.SatIn.sep sat_data0
    (Witness.SatIn.sep sat_data1 (Witness.SatIn.sep sat_psc sat_tabF (by decide +kernel))
    (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

theorem sat_psRest : SatIn (PsRest (σInit wI).1 (tAt cheW acW))
    [(0x500028920 + 0x2b8fc, 0x500028920 + 0x4c1e0)] := by
  unfold PsRest
  simp only [sbrA_tAt]
  exact Witness.SatIn.widen _ _ (by sat_tac) (by decide +kernel)

theorem sat_arrW : SatIn (ArrW (tAt cheW acW)) [(0x500028920 + 0x4c340, 0x500028920 + 0x601c0)] := by
  unfold ArrW
  simp only [sbrA_tAt]
  exact Witness.SatIn.widen _ _ (by sat_tac) (by decide +kernel)

theorem sat_dspW (e : Env) : SatIn (DspW e (tAt cheW acW))
    [(0x500028920 + 0x601e0, 0x500028920 + 0x60250)] := by
  unfold DspW
  simp only [sbrA_tAt]
  exact Witness.SatIn.widen _ _ (by sat_tac) (by decide +kernel)

theorem sat_gap : SatIn (InitGap cheW)
    [(0x500000000, 0x500028920), (0x500028920 + 0x60270, 0x500028920 + 0x60280)] := by
  unfold InitGap
  exact Witness.SatIn.sep (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel))
    (Witness.SatIn.block (Nat.le_refl _) (by decide +kernel)) (by decide +kernel)

end Kraken.Examples.Sbr.WitMem
