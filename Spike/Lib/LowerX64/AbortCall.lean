/-
**A lowered function's overflow abort inside the consumer's facts**
(x86-64): `userCallW_of_fn`'s premise `hab` (`Spike/Lib/LowerX64/UserCall.lean`),
the function's `.ovf` block (`abortN`) held back at a source control `c0`
(`Lag`), as a segment to any fragment inside `SFacts … Dt`. The twin of
`Spike/Lib/LowerA64/AbortCall.lean`.

The block is `Abort.Local.lb` (`Spike/Lib/X64AbortW.lean`, `seg_localW_lag`):
its states inside `SFacts` from `blkW_postO` (`Spike/Lib/Rt/X64RtW.lean`), its
call to `scc_rt_abort` the overflow path's obligations from `stubW_sfacts`
(`Spike/Lib/X64StubW.lean`). The abort's source (`AbJ`) is about to
overflow, and placed in the caller's cells (`placed_of_abSrc`), which lie
inside the frame (`rsOf_bounds`), off the abort call's region.

- `frame_mod8`: a valid frame's size is a multiple of 8.
- `lb_noRet`: the block has no `ret`.
- `hab_of`: the held-back abort label as a segment inside `SFacts … Dt`.
- `userCallW_main`: `userCallW_of_fn` with `hab_of` (the user `main`'s
  `UserCallW` from its code facts and the abort path's premises).

Where x86-64 differs from AArch64:
- the body's region is `%rbp`-based (`rbR` of the callee's region), the
  block at the frame's bottom `oB fr` (`%rsp = -fr.size`); the call pushes
  the return address, the stub's region `[-24, 16)` at `-fr.size - 16`, so
  the region holds `40` bytes below the frame (`hlo`; AArch64: `48`);
- the regions are 8-aligned (`hR8`; AArch64: 16-aligned), the frame's size
  a multiple of 8 from `FrameOk` (`frame_mod8`);
- an IR register's cell is at or above the frame's bottom (`rsOf_bounds`),
  so off the return address's cell and the stub's region; no separate
  bound on the cells is needed (AArch64's `rsOf_cell`);
- the stub's `write` call is a premise on the cells (`hsysIn`), and the
  callee's depth `D` holds the frame and the abort call's `48` bytes with
  the saved `%rbp` (`hD : fr.size + 48 ≤ D`).
-/
import Spike.Lib.LowerX64.UserCall
import Spike.Lib.X64StubW
import Spike.Lib.X64AbortPlace
import Spike.Lib.AbortSrc
import Spike.Lib.LowerX64.OvfCode

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.Rt.X64 (blockAtB)
open Scc.Sem (Marks Range)
open Spike.Lib.LowerNode (immsOf)
open Scc.Lower.Inv (lower0 Res)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl K0 blkPh noRetBlk noRet_false placed_of_abSrc)
open Spike.Lib.X64.Rt (InstOk UserCallW blkW_postO stackOff_callee)
open Spike.Lib.X64.Flow.Ret0 (StackOff CallerCells limA)
open Spike.Lib.X64.StubW (abortPhOk stubW_sfacts)
open Spike.Lib.AbortSrc (ovfReady_of_abSrc envSmall_of_abSrc)

/-- **A valid frame's size is a multiple of 8** (`frameOf`'s slots rounded
to 16, then the outgoing words). -/
theorem frame_mod8 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) : fr.size % 8 = 0 := by
  obtain ⟨areas, f, -, hsz⟩ := hf
  rw [hsz, frameOf_size]
  omega

theorem lb_noRet : noRetBlk Abort.Local.lb = true := by decide

section Abort

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **A function's overflow abort label held back at `c0` is a segment
inside `SFacts … Dt`** (to any `Q`): for a valid frame `fr` (`hf`), its
`.ovf` block in `cells` (the block `fnCodeOk` checks) with its phase facts,
both only when the walk `T` reaches a `+` (`hab`; else no state is at the
label), the abort code with the stub's `write` call and its
phase check (`hprog`, `hsysIn`, `hphs`), an instance's facts (`hI`), the
facts of `c0` (`hC0`), the layout's immediates the abort label's invariant
records (`himm`), the overflow exit as the memory side's abort site (`hrel`,
`htk`, `hk`, `hKex`, `hms`, `hK`), the write tail at the stub's `write`
for a region holding the stub's frame (`hwr`); in an 8-aligned region with 8-aligned bounds holding the frame and
the abort call's 40 bytes below it, and the frame record (`hlo`, `hhi`),
`rS` in the pool, not wrapping and off it (`hsub`, `hfit`, `hFO`). -/
theorem hab_of {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {p : Prog} {c0 : Ctl}
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {Dt : State → Prop} {lbl : Lbl}
    {ms : MemSide isa}
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) → blockAtB cells (ovfL fr) 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (hC0 : CFacts Λ lbl c0)
    (himm : Λ.imms = i)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.X64.pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.lo ≤ -24 → 16 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (Abort.N lab Abort.overflow c .sys) s c' → Dt s)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 40) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {fp ra : BitVec 64} {Q : Frag isa} :
    SegW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl ms
      (Lag p (· = c0) (At exe endPc R F (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0))) Q := by
  by_cases hT : ∃ x a b e, T (.let_ x (.add a b) e)
  case neg =>
    refine SegW.empty ?_
    rintro s c ⟨c', ⟨-, -, -, -, σ, -, -, ⟨⟨senv, hAb, -, hTc⟩, -⟩, -⟩, -, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := ovfReady_of_abSrc hAb
    exact hT ⟨x, a, b, e, he ▸ hTc⟩
  obtain ⟨hblk, hphA⟩ := hab hT
  have h8 := frame_mod8 hf
  have hs8 : (oB fr).sp % 8 = 0 := by simp only [oB]; omega
  have hcode := ovfCode_codeAt hI.lays hI.endOk hblk
  rw [ovfBlk_eq_lb] at hblk
  have hW0 := blkW_postO (rS := rS) (Λ := Λ) (lbl := lbl) (R := R) (F := F)
    (n := ⟨(_root_.Executable.labels exe).label (ovfL fr), oB fr,
      LagJ p (· = c0) (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0).J⟩)
    hI hblk (by rw [hI.labOk, Spike.Lib.X64.Flow.ofNat_zero']) (Abort.Local.lb_ok (oB fr) hs8) hR
    (by simp only [oB]; omega) (by simp only [oB]; omega) hR8 hl hh (by rintro σ c ⟨-, -, -, rfl⟩; exact hC0) hphA
    (fun _ _ _ k hk r => (noRet_false lb_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hfit hFO
  have hW := BlkW.mapC (W' := fun s c => SFacts Λ μ own rS Tk lbl s c Dt) rfl rfl hW0
    fun σ c h => ⟨c, h, fun _ hs => hs.dt_mono fun _ h => h.elim⟩
  refine Abort.Local.seg_localW_lag (o := oB fr) (pcA := (_root_.Executable.labels exe).label (ovfL fr))
    (C := (· = c0)) (J := (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0).J) hF hR
    (by simp only [oB]; omega) (by simp only [oB]; omega) hs8 hK hcode hW ?_
  intro R' F' hR' hlo' hhi' hF' hFF' hR'e c hJc hmem
  subst hR'e
  obtain ⟨σ0, ⟨⟨senv, hAb, -, -⟩, -⟩, -⟩ := hJc
  have hkc8 : ((oB fr).sp - 8 - 8) % 8 = 0 := by omega
  have hb8' : (R.callee ((oB fr).sp - 8 - 8) (-24) 16).base.toNat % 8 = 0 := addr_toNat_mod8 R hR8 hkc8
  refine stubW_sfacts hI hprog hsysIn hphs hR' hb8' hlo' hhi' (by show (-24 : Int) % 8 = 0; decide)
    (by show (16 : Int) % 8 = 0; decide) hF' hsub hfit ?_
    (ovfReady_of_abSrc hAb) (envSmall_of_abSrc hAb) ?_ hrel htk hk hKex hms hK (hwr _ _ hlo' hhi' _)
  · intro m h
    refine stackOff_callee hR hR8 hl hh (by simp only [oB]; omega) (by decide) (by simp only [oB]; omega) hkc8
      (hFO m (hFF' m h)) ?_
    intro k hk hn
    obtain ⟨mC, σC, σ1, hA, -, -, he⟩ := hmem m h
    rw [he k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro s h
    obtain ⟨mC, σC, σ1, hA, hsl, hJ1, he⟩ := hmem s.st.1 h
    obtain ⟨senv1, hAb1, hi1, -⟩ := hJ1.1.1
    refine placed_of_abSrc hAb1 (addr := R.addr) (fun r k hr => ?_) (himm ▸ hi1)
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    have hk : R.Off k := ⟨h2, by omega, by omega⟩
    have hn : ¬ (R.callee ((oB fr).sp - 8 - 8) (-24) 16).Off (k - ((oB fr).sp - 8 - 8)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee, oB] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Mem.loadInt s.st.1.dmem (R.addr k) 8).map (BitVec.ofInt 64) = some (σ1.slot k)
    rw [he k hk hn, hj, Option.map_some, hjs, hsl k (by simp only [oB]; omega)]

/-- **The user `main` is `scc_rt_main`'s user function inside `SFacts`**,
its overflow abort from the function's `.ovf` block (`userCallW_of_fn`
with `hab_of` at the start `X64Consumer.c0`, in the body's region `rbR`
of the callee's): the premises of both, the depth `D` holding the frame,
the abort call's 40 bytes and the saved `%rbp` (`hD`); the walk `InWalk d`,
the abort block's premises only for a nonempty body (`insts_ne_of_add_suffix`). -/
theorem userCallW_main {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {fr : Scc.Emit.X64.Frame} {r : Res}
    {fn entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true) (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn cells fr entry 0 r.insts r.ret = true)
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isa} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hR8 : R.base.toNat % 8 = 0) (hZ8 : Z.toInt % 8 = 0)
    (hD : (fr.size : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hphB : bodyPhOk okPc ph (fun _ => false) lab cells fr entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts Λ lbl Spike.Lib.X64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m →
      StackOff rS (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) m)
    (hab : r.insts ≠ [] → blockAtB cells (ovfL fr) 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = immsOf d)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.X64.pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.lo ≤ -24 → 16 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (Abort.N lab Abort.overflow c .sys) s c' → Dt s) :
    UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D (Int64.ofInt fr.size)
      (UPost [d] lbl Spike.Lib.X64Consumer.c0) ra Spike.Lib.X64Consumer.c0 tp :=
  userCallW_of_fn hd hf h1 hpro hr hbody hI hR8 hZ8 (by omega) hD8 hphB hphP hC0 hmr hun hsub hfit hFO hK
    fun F' hR0 hb0 hF' hFF _ _ =>
      hab_of hf hI (fun ⟨_, _, _, _, hT⟩ => hab (Spike.Lib.LowerNode.insts_ne_of_add_suffix hr hT)) hprog hsysIn
        hphs hC0 himm hrel htk hk hKex hms hK hwr
        (rbR_ok hR0 (by show -D ≤ _; omega) (by show (0 : Int) ≤ 8; decide)) (addr_toNat_mod8 _ hb0 (by decide))
        (by show -D + 8 ≤ _; omega) (by show (0 : Int) ≤ 8 + 8; decide) (by show (-D + 8) % 8 = 0; omega)
        (by show (8 + 8 : Int) % 8 = 0; decide) (rbR_fstable hR0 (by show -D ≤ _; omega) (by show (0 : Int) ≤ 8; decide) hF') hsub hfit
        fun m h => stackOff_rbR hR0 (by show -D ≤ _; omega) (by show (0 : Int) ≤ 8; decide)
          (hFO m (hFF m h).1 (hFF m h).2)

end Abort

end Spike.Lib.LowerX64
