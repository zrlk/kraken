/-
**`hst0_ofW`'s `hxa` from `h1`'s statement** (wake.w, AArch64; H0 part F): at the root's immediate table `IW := immsW2 Λ0 wakeImms`,
the box's landing past its store (`bX` at `msBot E []`, `wc_main`'s
region and frame condition) with main's thread pointer is a `Box`, so
`h1`'s statement (`WakeRoot.H1R` at `msBot E []`) puts it in `inv1R`, and
the landing is in `msBot E []`'s allocation fragment (`AllocLand` from
`bX`'s allocator fact, `I2`'s `inv1` disjunct).

- `wJ0_c0W`: `wc_main`'s entry invariant at `JS … c0W` pins the source at
  `c0W` and `x0` at the first TCB.
- `load_of_off`: a stack range's words load, off a region by `StackOff`,
  inside it by `Abs`.
- `box_landing`: the landing is a `Box`, given the child's stack unmapped
  (`KeepUn.U`, `hu`) and `wc_main`'s frame condition inside `F0` (`hF0`).
- `hxa_R`: `hst0_ofW`'s `hxa`, given `H1R`, `hF0` and the open `hUn1`.
-/
import Spike.Lib.A64WakeStartH0R
import Spike.Lib.A64WakeTakeFLy

namespace Spike.Lib.A64.WakePh.Hxa

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize Pz)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (bX)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib (FragS)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeC0 (c0W)

/-- **`wc_main`'s entry invariant at `JS … c0`**: the source at `c0`, `x0`
the first TCB. -/
theorem wJ0_c0W {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Ctl} {σC σ : Spike.Lib.A64.Flow.AS} {c : Ctl}
    (h : wJ0 (wNC L.lab (JS L k0 c0)).J σC σ c) :
    c = c0 ∧ σ.regs.X0.toBitVec = pinA L.lab + 0#64 + 8#64 := by
  obtain ⟨rfl, ⟨σe, ⟨⟨hc, -, -⟩, hx0⟩, -, -, h48, -, -⟩, hX0C, -⟩ := h
  refine ⟨hc, ?_⟩
  show σC.regs.X0.toBitVec = _
  rw [hX0C, h48, hx0]

/-- **A stack range's words load** when those off a region load
(`StackOff`) and the region's cells are an abstraction's (`Abs`), the
region's base and bounds word-aligned. -/
theorem load_of_off {R : Region} {rS : Scc.Sem.Range} {o : Spike.Lib.A64.Flow.SO} {m : MachineData}
    {σ : Spike.Lib.A64.Flow.AS} (hR : R.OK) (hal : R.base.toNat % 8 = 0) (hlo8 : R.lo % 8 = 0)
    (hhi8 : R.hi % 8 = 0) (hSO : Spike.Lib.A64.Flow.Ret0.StackOff rS R m) (hA : Spike.Lib.A64.Flow.Abs R o m σ) :
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) → (Mem.loadInt m.dmem (BitVec.ofNat 64 a) 8).isSome := by
  intro a h8 ha ha7
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact hSO a h8 ha ha7 hout
  · have hk : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
    have he := R.addr_toNat hR hk
    have hlt := (R.addr ((a : Int) - R.base.toNat)).isLt
    obtain ⟨j, hj, -⟩ := hA.slot _ hk
    have ea : BitVec.ofNat 64 a = R.addr ((a : Int) - R.base.toNat) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    rw [ea, hj]; rfl

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "MS" => Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPW" => TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

/-- **The box's landing is a `Box`** at `msBot E []`: `wc_main`'s region
`wR (swR v (-384) 0) 336` at the first stack's top, its frame condition
`wF … FS …`, the entry node at `JS … c0W`, the thread pointer the first
TCB; the source at `c0W` past its `new`; main's stack owned (`StackOff`
off the region, `Abs` inside), the child's stack unmapped (`hu`). -/
theorem box_landing (E : Entry) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {F0 : MachineData → Prop}
    (hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m → F0 m)
    {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl}
    (hA : At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (bX MS (Ly).lab ((JW) σC) l A) s c)
    (htp : TPW s) (hu : Spike.Lib.A64.KeepUn.U R1 s) :
    Spike.Lib.A64.Flow.WakeWc.Box (Ly) MS F0 l A 1 s c := by
  have hA0 := hA
  obtain ⟨he, hn, hdc, hpc, σ, hAbs, hFm, hJ⟩ := hA
  have hFm' := hFm
  obtain ⟨⟨-, ⟨hv, -⟩, -⟩, -, -⟩ := hFm'
  subst hv
  -- the first stack's top and its region
  have hst := (Ly).stacks_sub
  have hsal := (Ly).stacks_al
  have hpf := (Ly).pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hT : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat = (Ly).stacksA.toNat + 16384 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.top0_toNat _
  have hsw : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  have hal0 : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0).base.toNat % 16 = 0 := by
    show (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0
    rw [hT]; omega
  have hFS : Spike.Lib.A64.Flow.FStable (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0)
      (FS (Ly) RS 384 0#64 (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64)) :=
    Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable (Spike.Lib.PlaceW.wf_link_of_placeW IW hp)
      (Spike.Lib.A64.Rt.rS0_sub (Ly)) hsw (by decide) (by decide)
      (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
      (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
      (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
      (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly)))
  obtain ⟨hRok, hRal, hRF⟩ := Spike.Lib.A64.Flow.WakeM.wR_ok (D := 336) (by decide) (by decide) hsw hal0 hFS
    (by simp [swR]) (by simp [swR]) m0 σC
  have hb : ((wR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0) 336).base.toNat : Int) =
      (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat + -48 :=
    Spike.Lib.Region.callee_base (hi' := 0) hsw (kc := -48) (lo' := -336)
      (by simp [swR]) (by decide) (by simp [swR])
  have hb' := hb
  rw [hT] at hb'
  have hRlo : (wR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0) 336).lo = -336 := rfl
  have hRhi : (wR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0) 336).hi = 0 := rfl
  have hSO := Spike.Lib.A64.WakePh.StartPlaceLy.stackOff_r0_box hp IW _ hFm
  have hr0 : (Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab).lo = (Ly).stacksA.toNat := by
    show (Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat = _
    rw [(Ly).lab_stacks, BitVec.add_zero]
  have hr0s : (Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab).size = 16384 := rfl
  -- the source at `c0W` past its `new`
  obtain ⟨q, ⟨σe, hJe, -⟩, h72, hc, ob, hAo, hlt⟩ := hJ
  obtain ⟨hq0, -⟩ := wJ0_c0W hJe
  have ht := q.2.term
  rw [hq0] at ht
  obtain ⟨hx, ha, hee⟩ := Expr.let_.inj ht
  have ha' := Op.new.inj ha
  have hev := q.2.ev
  rw [hq0, ← ha'] at hev
  have hτ : q.1.τ = .int := (Prod.mk.inj (Option.some.inj hev)).1.symm
  rw [← hx, ← hee, hτ, hq0] at hc
  subst hc
  have hpin : (Ly).pinA.toNat < 2 ^ 32 := (Ly).words_small _ (Ly).pin_mem
  have hp0 := Spike.Lib.PlaceW.pinA_toNat_ofPlaceW hp IW
  have hpin8 : (pinA (Ly).lab + 0#64 + 8#64).toNat = (Ly).pinA.toNat + 8 := by
    rw [Spike.Lib.A64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨_, _, _, _, ⟨hRok, hRal, hRF, by rw [hRlo]; decide, by rw [hRhi]; decide, by omega, ?_⟩, ?_, hF0 _ m0 σC,
    ⟨⟨_, σC, rfl⟩, fun σe c h => ?_, by omega⟩, ⟨hA0, htp, ?_⟩, rfl, ⟨rfl, rfl, rfl, rfl⟩, ⟨?_, hu⟩,
    ⟨Spike.Lib.A64.WakePh.StartPlaceLy.wF_takeMem hp IW hA13,
      Spike.Lib.WakeBoxW.wF_dmem Spike.Lib.WakeBoxW.fS_dmem, by rw [hRhi]; decide,
      Spike.Lib.A64.WakePh.StartPlaceLy.stackOff_r0_box hp IW, by rw [hRlo]; decide, by rw [hRhi]; decide⟩⟩
  · -- the words at `0` and `8` above the region: `scc_rt_main`'s frame, off the region
    intro m hm k h8 h0 h16
    have hR' : (⟨(wR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0) 336).base, 0, 16⟩ :
        Region).OK := ⟨by simp, by simp only; omega⟩
    have ek := Spike.Lib.Region.addr_toNat_of hR' (k := k) (by simp only; omega) (by simp only; omega)
    simp only at ek
    have hs := Spike.Lib.A64.WakePh.StartPlaceLy.stackOff_r0_box hp IW m hm
      (Region.addr ⟨(wR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-384) 0) 336).base, 0, 16⟩ k).toNat
      (by omega) (by rw [Scc.Sem.Range.contains, hr0, hr0s]; omega)
      (by rw [Scc.Sem.Range.contains, hr0, hr0s]; omega) (.inr (by rw [hRhi]; omega))
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hs
    exact hs
  · -- the call's slots in the pool
    intro k h1 h2
    have := Spike.Lib.Region.addr_toNat_of hRok (k := k) (by rw [hRlo]; omega) (by rw [hRhi]; omega)
    constructor <;> omega
  · -- `x0` the first TCB
    obtain ⟨-, hx⟩ := wJ0_c0W h
    show σe.regs.X0.toBitVec.toNat = _
    rw [hx, hpin8, hp0]; rfl
  · show (pinA (Ly).lab + 0#64 + 8#64).toNat = _
    exact hpin8
  · -- main's stack owned: off the region `StackOff`, inside it `Abs`
    refine ⟨by rw [Scc.Sem.Range.Sub, hr0, hr0s]; exact hst, fun a h8 ha ha7 => ?_⟩
    simp only [Scc.Sem.A64.privLoad, Option.isSome_map]
    exact load_of_off hRok (by omega) (by rw [hRlo]; decide) (by rw [hRhi]; decide) hSO hAbs a h8 ha ha7

/-- **`hst0_ofW`'s `hxa`**: the box's landing with main's thread pointer is
in `msBot E []`'s allocation fragment. The cell `A` lands in the arena
(`AllocLand`, from `bX`'s allocator fact at `off = 8`, `units ≥ 1`), and
the landing, a `Box` (`box_landing`), is in `inv1R` by `h1`'s statement
(`I2`'s `inv1` disjunct).

OPEN `hUn1` (run-level; the second take's site frame `Pz r1` follows from it): the
child's stack unmapped at the landing (`KeepUn.U`). Its discharge: `U r1`
holds of the loaded image and is kept by every step up to the landing
(`KeepUn.SegW.keepUn`). -/
theorem hxa_R (E : Entry) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {F0 : MachineData → Prop} (h1 : Spike.Lib.WakeRoot.H1R hp IW ls0 Ctx MS F0 E)
    (hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m → F0 m)
    /- OPEN root obligation (run-level): the child's stack unmapped at the landing -/
    (hUn1 : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
        (bX MS (Ly).lab ((JW) σC) l A) s c → TPW s → Spike.Lib.A64.KeepUn.U R1 s) :
    ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
        (bX MS (Ly).lab ((JW) σC) l A) s c → TPW s → (MS).xa l A 1 s c := by
  intro v m0 σC l A s c hl hA htp
  have hB := box_landing hp ls0 Ctx E hA13 hF0 hA htp (hUn1 v m0 σC l A s c hl hA htp)
  obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := hA
  have hf : (MS).off 1 q.1.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
  have hu : 1 ≤ (MS).units 1 q.1.τ := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
  have hcl : 2 ≤ (MS).cells := show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  have hAL : Spike.Lib.HeapLand.AllocLand (Spike.Lib.WakeOD.arW hp IW).heap (Spike.Lib.WakeOD.arW hp IW).cells A 1 := by
    show (MS).heap + 8 ≤ A ∧ A + 8 * 1 ≤ (MS).heap + 16 * (MS).cells ∧ 1 + 1 ≤ (MS).cells
    rw [hf] at hAo; omega
  exact ⟨hAL, .inr ⟨l, A, 1, hl, hAL, rfl, rfl, (h1 l A 1 hl hAL).2.1 s c hB⟩⟩

end Spike.Lib.A64.WakePh.Hxa

/-- info: 'Spike.Lib.A64.WakePh.Hxa.box_landing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Hxa.box_landing

/-- info: 'Spike.Lib.A64.WakePh.Hxa.hxa_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Hxa.hxa_R
