/-
**A lowered function's overflow abort inside the consumer's facts**
(AArch64): `userCallW_of_fn`'s premise `hab` (`Spike/Lib/LowerA64/UserCall.lean`),
the function's `.abort_overflow` block (`abortN`) held back at a source
control `c0` (`Lag`), as a segment to any fragment inside `SFacts … Dt`.

The block is `A64.Abort.Local.lb` (`Spike/Lib/A64AbortW.lean`, `seg_localW_lag`):
its states inside `SFacts` from `blkW_postO` (`Spike/Lib/Rt/A64RtW.lean`), its
call to `scc_rt_abort` the overflow path's obligations from `stubW_sfacts`
(`Spike/Lib/A64StubW.lean`). The abort's source (`AbJ`) is about to
overflow, and placed in the caller's cells (`placed_of_abSrc`), which lie
off the abort call's 48 bytes (`rsOf_cell`).

- `rsOf_cell`: an IR register's cell is 8-aligned, inside the frame, at
  least 24 bytes below its top and at or above the outgoing area.
- `hab_of`: the held-back abort label as a segment inside `SFacts … Dt`.
- `userCallW_main`: `userCallW_of_fn` with `hab_of` (the user `main`'s
  `UserCallW` from its code facts and the abort path's premises).
-/
import Spike.Lib.LowerA64.UserCall
import Spike.Lib.A64StubW
import Spike.Lib.A64AbortPlace
import Spike.Lib.AbortSrc
import Spike.Lib.A64Ret0I
import Spike.Lib.LowerA64.OvfCode

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (blockAt)
open Scc.Sem (Marks Range)
open Spike.Lib.Form (lookupS SEnv)
open Spike.Lib.LowerNode (AbSrc immsOf)
open Spike.Lib.A64Consumer (CFacts SFacts Own Lbl blkPh noRetBlk noRet_false placed_of_abSrc)
open Spike.Lib.A64.Rt (InstOk blkW_postO)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (stackOff_callee)
open Spike.Lib.A64.StubW (abortPhOk stubW_sfacts)
open Spike.Lib.AbortSrc (ovfReady_of_abSrc envSmall_of_abSrc)

/-- **An IR register's cell** (`rsOf`) in a valid frame: 8-aligned, at or
above the frame's bottom (the outgoing area), at least 24 bytes below its
top (the saved pair above). -/
theorem rsOf_cell {cx : FnCtx} (hf : FrameOk cx) {r : Scc.IR.Reg} {k : Int} (h : rsOf cx r = some k) :
    k % 8 = 0 ∧ -(cx.frame : Int) ≤ k ∧ k + 24 ≤ 0 ∧ 0 ≤ k + cx.frame := by
  unfold rsOf at h
  cases ho : cx.slotOff r with
  | error _ => simp [ho] at h
  | ok off =>
    simp only [ho, Option.some.injEq] at h
    obtain ⟨i, hi, -, rfl⟩ := slotOff_index ho
    have h1 := le_align16 (8 * cx.slots.length + 16)
    have h2 := align16_mod (8 * cx.slots.length + 16)
    unfold FrameOk at hf
    omega

theorem lb_noRet : noRetBlk A64.Abort.Local.lb = true := by decide

section Abort

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **A function's overflow abort label held back at `c0` is a segment
inside `SFacts … Dt`** (to any `Q`): for a function context `cx` with a
valid 16-aligned frame (`hf`, `h16`), its `.abort_overflow` block in `prog`
(the block `fnCodeOk` checks: `ovfCode_of_placeOK`) with its phase facts, both
only when the walk `T` reaches a `+` (`hab`; else no state is at the label),
the abort code with its phase check
(`hprog`, `hphs`), an instance's facts (`hI`), the facts of `c0` (`hC0`),
the layout's immediates the abort label's invariant records (`himm`), the overflow exit
as the memory side's abort site (`hrel`, `htk`, `hk`, `hKex`, `hms`, `hK`),
the write tail at the stub's `write` (`hwr`); in a 16-aligned region with
8-aligned bounds holding the frame and the abort call's 48 bytes (`hlo`,
`hhi`), `rS` in the pool, not wrapping and off it (`hsub`, `hfit`, `hFO`). -/
theorem hab_of {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {p : Prog} {c0 : Ctl} {cx : FnCtx}
    (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop} {lbl : Lbl}
    {ms : MemSide isaLSE2}
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (hC0 : CFacts Λ lbl c0)
    (himm : Λ.imms = i)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.A64.pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (A64.Abort.N lab A64.Abort.overflow c .svc) s c' → Dt s)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {fp ra : BitVec 64} {Q : Frag isaLSE2} :
    SegW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl ms
      (Lag p (· = c0) (At exe endPc R F (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0))) Q := by
  by_cases hT : ∃ x a b e, T (.let_ x (.add a b) e)
  case neg =>
    refine SegW.empty ?_
    rintro s c ⟨c', ⟨-, -, -, -, σ, -, -, ⟨⟨senv, hAb, -, hTc⟩, -⟩, -⟩, -, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := ovfReady_of_abSrc hAb
    exact hT ⟨x, a, b, e, he ▸ hTc⟩
  obtain ⟨hblk, hphA⟩ := hab hT
  have hge := frame_ge16 hf
  have hR8 : R.base.toNat % 8 = 0 := by omega
  rw [ovfBlk_eq_lb] at hblk
  have hcode := code_of hI.lays hI.endOk hblk (q := (_root_.Executable.labels exe).label (cx.local "abort_overflow"))
    (ofNat4_zero _)
  have hW0 := blkW_postO (rS := rS) (Λ := Λ) (lbl := lbl) (R := R) (F := F)
    (n := ⟨(_root_.Executable.labels exe).label (cx.local "abort_overflow"), ⟨-(cx.frame : Int), []⟩,
      LagJ p (· = c0) (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).J⟩)
    hI hblk (by rw [hI.labOk, ofNat4_zero]) (A64.Abort.Local.lb_ok R.lo R.hi cx.frame) hR hal (Int.le_refl _)
    (Int.le_refl _) (by rintro σ c ⟨-, -, -, rfl⟩; exact hC0) hphA
    (fun _ _ _ k hk r hr => (noRet_false lb_noRet k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO
  have hW := BlkW.mapC (W' := fun s c => SFacts Λ μ own rS Tk lbl s c Dt) rfl rfl hW0
    fun σ c h => ⟨c, h, fun _ hs => hs.dt_mono fun _ h => h.elim⟩
  refine A64.Abort.Local.seg_localW_lag (fr := cx.frame) (C := (· = c0))
    (J := (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).J) hF hR hal hlo hhi (by omega)
    (by omega) hK hcode hW ?_
  intro R' F' hR' hal' hlo' hhi' hF' hFF' hR'e c hJc hmem
  subst hR'e
  obtain ⟨σ0, ⟨⟨senv, hAb, -, -⟩, -⟩, -⟩ := hJc
  refine stubW_sfacts hI hprog hphs hR' hal' hlo' hhi' rfl rfl hF' hsub hfit ?_
    (ovfReady_of_abSrc hAb) (envSmall_of_abSrc hAb) ?_ hrel htk hk hKex hms hK (hwr _ _ hal' hlo' hhi' _)
  · intro m h
    refine stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) (by omega) (hFO m (hFF' m h)) ?_
    intro k hk hn
    obtain ⟨mC, σC, σ1, hA, -, -, he⟩ := hmem m h
    rw [he k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro s h
    obtain ⟨mC, σC, σ1, hA, hsl, hJ1, he⟩ := hmem s.st.1 h
    obtain ⟨senv1, hAb1, hi1, -⟩ := hJ1.1.1
    refine placed_of_abSrc hAb1 (addr := R.addr) (fun r k hr => ?_) (himm ▸ hi1)
    obtain ⟨h8, h1, h2, h3⟩ := rsOf_cell hf hr
    have hk : R.Off k := ⟨h8, by omega, by omega⟩
    have hn : ¬ (R.callee (-(cx.frame : Int)) (-48) 0).Off (k - -(cx.frame : Int)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Mem.loadInt s.st.1.dmem (R.addr k) 8).map (BitVec.ofInt 64) = some (σ1.slot k)
    rw [he k hk hn, hj, Option.map_some, hjs, hsl]

/-- **The user `main` is `scc_rt_main`'s user function inside `SFacts`**,
its overflow abort from the function's abort block (`userCallW_of_fn` with
`hab_of` at the start `A64Consumer.c0`, the walk `InWalk d`): the premises of
both, the abort block's only for a nonempty body (`insts_ne_of_add_suffix`). -/
theorem userCallW_main {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {cx : FnCtx} {r : Scc.Lower.Inv.Res}
    {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : Scc.Lower.Inv.lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn prog cx entry 0 r.insts r.ret = true)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hD : (cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hphB : bodyPhOk okPc ph (fun _ => false) lab cx entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : Spike.Lib.LowerA64.ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts Λ lbl Spike.Lib.A64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m →
      StackOff rS (R.callee (-Z.toInt) (-D) 0) m)
    (hab : r.insts ≠ [] → blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = immsOf d)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.A64.pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (A64.Abort.N lab A64.Abort.overflow c .svc) s c' → Dt s) :
    Spike.Lib.A64.Rt.UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D
      (Int64.ofInt cx.frame) (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 tp :=
  userCallW_of_fn hd hf h1 h16 hpro hr hbody hI hD hD8 hphB hphP hC0 hmr hun hsub hfit hFO
    fun F' hR0 hal0 hF' hFF _ _ =>
      hab_of hf h16 hI
        (fun ⟨_, _, _, _, hT⟩ => hab (Spike.Lib.LowerNode.insts_ne_of_add_suffix hr hT)) hprog hphs hC0 himm
        hrel htk hk hKex hms hK hwr hR0 hal0
        (by show -D ≤ _; omega) (Int.le_refl 0) (by show (-D) % 8 = 0; omega) rfl hF' hsub hfit
        fun m h => hFO m (hFF m h).1 (hFF m h).2

end Abort

end Spike.Lib.LowerA64
