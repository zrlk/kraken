/-
**`hello_wc_mid_hatW` under an outside move that moves the callee's states**
(AArch64, `hatA`; the hello twin of
`Spike/Lib/A64WakeWcHatK.lean` at `wc_main`'s frame 144): the same end at
main's `clone` `svc`, the segment (callee included) inside `W ∧ NoMsrAt`
(`SegW.keepTPA`) rather than `NoMsrW W K`, so `K` may move states inside
`scc_rt_thread_init` (its take), given that `K` keeps the thread pointer
(`hKt`). The callee's segment is asked at the ghosts' facts (`MidG`,
`FrMGH`) with the second stack `r1Of` unmapped at its entry (`Pz r1Of`).

Reused from wake as is (layout generic): `takeCK_fK`, `takeCK_tp`,
`SegW.keepTPA`, `KeepUn.SegW.keepUn`.

- `WcMidWH.antiF₂`: the node obligations at a stronger late frame condition;
- `hello_wc_mid_hatK`: `hello_wc_mid_segW`'s composite, `r1Of` kept unmapped
  up to the call (`KeepUn.SegW.keepUn`, off the clone's and the take site's
  pcs: `OffCH`), its callee given the ghosts' facts, then `SegW.keepTPA` and
  `wcNSH_base`;
- `takeCKH_kR`, `stackM_r1H`: the take of `r1Of` or a `clone` refusal keeps
  `R`'s cells when `R` ends below the second stack (`R.hi ≤ 80`, `R`'s base
  80 below it: `BoxPureH`'s); no write inside such an `R` breaks
  `StackM r1Of`.

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloWcHat
import Spike.Lib.A64HelloWcK1
import Spike.Lib.A64HelloWcMidW
import Spike.Lib.A64HelloWcNoMsr
import Spike.Lib.A64WakeWcHatK

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (tiN tiX StackM)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH wcNSH hello_wc_sp6_segW)
open Spike.Lib.A64.Flow.WakeWc (AGB MidG kOf tiQ okb_of_tpXa stOk_tpXa tcbOkGA_tpXa resOkA_tpXa)
open Spike.Lib.A64.Rt (TcbOkGA hdrA RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (NoMsrAt TP tpXa)
open Spike.Lib.A64ConsumerA (TakeCK)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.A64Consumer (Pz)

section Anti

variable {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F₂ F₂' : MachineData → Prop} (hf : ∀ m, F₂' m → F₂ m)
include hf

/-- **From the box's store to the `svc` at a stronger late frame condition**
(`F₂' ⊆ F₂`: fewer states at `.sp6`'s nodes). -/
theorem WcMidWH.antiF₂ {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcMidWH W K exe endPc R F F₂ ms J1 S Q) : WcMidWH W K exe endPc R F F₂' ms J1 S Q := by
  have hb : ∀ {n blk}, BlkW W K exe endPc R F₂ n blk → BlkW W K exe endPc R F₂' n blk :=
    fun h s σ c he hn hd hpc hA hD hJ => h s σ c he hn hd hpc hA (hf _ hD) hJ
  have hn : ∀ {n}, NodeW W K exe endPc R F₂ n → NodeW W K exe endPc R F₂' n :=
    fun h s c ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hd, hpc, σ, hA, hf _ hD, hJ⟩
  exact ⟨h.res, h.sp3, h.sp4, fun c0 sl me cA fr hM => let h6 := h.sp6 c0 sl me cA fr hM
    ⟨hb h6.n6, hn h6.n6f, hb h6.n6a⟩⟩

end Anti

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

set_option maxHeartbeats 1600000 in
/-- **`hello_wc_mid_hatW` inside `W ∧ NoMsrAt`**: its premises, the node
obligations (`hW`) and the callee (`hti`, given the ghosts' facts) inside
`W ∧ NoMsrAt` at `tpXa ms tp`, under an outside move keeping the thread
pointer (`hKt`). The second stack `r1Of` is unmapped at the entry and kept
unmapped up to the call (`hKu` off the clone and the take site, `OffCH`;
`KeepUn.SegW.keepUn`): the callee is promised `Pz r1Of` at its entry
(`hello_wc_sp4_call_segW`). -/
theorem hello_wc_mid_hatK {tp : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -400) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcMidWH (fun s c => W s c ∧ NoMsrAt s) K exe endPc R F F₂ (tpXa ms tp) J1 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rARH R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2QH g c0))
      ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0))
    (htid : let t := tH (_root_.Executable.labels exe).label
      ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-192) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hKt : ∀ s s', K s s' → TP tp s → TP tp s')
    (hKu : ∀ s c, W s c ∧ NoMsrAt s → OffCH exe s c → ∀ s', K s s' →
      U (r1Of (_root_.Executable.labels exe).label) s → U (r1Of (_root_.Executable.labels exe).label) s')
    (hti : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
      let t := tH (_root_.Executable.labels exe).label
      ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => W s c ∧ NoMsrAt s) K p lbl (tpXa ms tp)
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e) s c ∧
            Pz (r1Of (_root_.Executable.labels exe).label) s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c ∧ Q l A c) ∧
        U (r1Of (_root_.Executable.labels exe).label) s ∧ TP tp s)
      (fun s c => ∃ sl me cA fr, MidG S c cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH (_root_.Executable.labels exe).label c (tH (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) sl me cA fr) s c ∧
        (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 ∧ TP tp s) := by
  let lab := (_root_.Executable.labels exe).label
  have hWo := WcMidWH.and hW (wcMidW_offCH hp)
  have hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
    fun s s' hk hD k hk' hn => hKR s s' hk hD k hk' fun ⟨h1, h2, h3⟩ =>
      hn ⟨h1, by simp only [Region.callee] at h2 ⊢; omega, by simp only [Region.callee] at h3 ⊢; omega⟩
  -- `hello_wc_mid_segW`'s composite to the call node, `r1Of` kept unmapped; then the call and `.sp6`
  let NI : Ctl × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × BitVec 64 × BitVec 64 ×
      (BitVec 64 × BitVec 64) → Frag isaLSE2 := fun g s c =>
    At exe endPc R F (wcNIH lab g.1 (tH lab) g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2) s c ∧
      (MidG S g.1 g.2.2.2.1 ∧ FrMGH J1 g.2.2.2.2 g.2.1 g.2.2.1)
  have hG : ∀ (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64)
      (fr : BitVec 64 × BitVec 64),
      SegW (fun s c => (W s c ∧ NoMsrAt s) ∧ OffCH exe s c) K p lbl (tpXa ms tp)
        (fun s c => At exe endPc R F (wcN3H lab c0 sl me cA fr) s c ∧ (MidG S c0 cA ∧ FrMGH J1 fr sl me))
        (fun s c => ∃ g, NI g s c) :=
    fun c0 sl me cA fr => SegW.of_imp fun hM =>
      ((hello_wc_sp3_segW hp hend hF hR hal (by omega) hhi (hWo.sp3 c0 sl me cA fr hM)
        (fun g => stOk_tpXa (hhdr c0 g)) (fun g => tcbOkGA_tpXa (htcb c0 g)) hFK hKR).seq
        (hello_wc_sp4_pre_segW hp hend hF hR hal (by omega) hhi (hWo.sp4 c0 sl me cA fr hM) htid)).mono_post
        fun _ _ h => ⟨(c0, sl, me, cA, fr), h, hM⟩
  have hC : ∀ g, SegW (fun s c => W s c ∧ NoMsrAt s) K p lbl (tpXa ms tp) (fun s c => NI g s c ∧ U (r1Of lab) s)
      (fun s c => ∃ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH lab c0 (tH lab) (kOf lab) sl me cA fr) s c) := fun g =>
    (SegW.of_imp (P := At exe endPc R (fun m => F m ∧ Pz (r1Of lab) m)
        (wcNIH lab g.1 (tH lab) g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2))
      fun hM => ((hello_wc_sp4_call_segW (P := Pz (r1Of lab)) hF hR hal hlo hhi hF₂ hFK hKR4
        (hti g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 hM)).seq
        (hello_wc_sp6_segW hp hend hF₂s hR hal (by omega) hhi (hW.sp6 g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 hM))).mono_post
        fun _ _ h => ⟨g.1, g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2, hM.1, hM.2, h⟩).mono_pre
      fun _ _ ⟨⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩, hu⟩ =>
        ⟨⟨he, hn, hdc, hpc, σ, hA, ⟨hD, A64Consumer.pz_of_unowned (by show 0 < 16384; decide) hu.2⟩, hJ⟩, hM⟩
  obtain ⟨inv, hP, hiW, hcl⟩ := (hello_wc_res_segW hp hend hF hR hal (by omega) hhi hWo.res
    (fun q l A hQ => hfr ⟨q.1, okb_of_tpXa q.2⟩ l A hQ) fun g => resOkA_tpXa (hres g)).seq
    ((SegW.exists_pre (P := fun (g : Ctl × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × BitVec 64 ×
        BitVec 64 × (BitVec 64 × BitVec 64)) s c =>
      At exe endPc R F (wcN3H lab g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2) s c ∧
        (MidG S g.1 g.2.2.2.1 ∧ FrMGH J1 g.2.2.2.2 g.2.1 g.2.2.1))
      fun g => hG g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).mono_pre fun s c ⟨x, h⟩ => by
        obtain ⟨sl, me, cA, fr, hM, hGm, h⟩ := rXH_wcN3H h
        exact ⟨(c, sl, me, cA, fr), h, hM, hGm⟩)
  -- at `unXa` (`Out.mono_xa`), then `r1Of` kept unmapped to the call node
  have hseg := (A64.KeepUn.SegW.keepUn (r := r1Of lab) hK (ms := tpXa ms tp) ⟨inv, hP, hiW, fun s c hi =>
    ⟨fun hk => A64ConsumerA.Out.mono_xa ((hcl s c hi).1 hk) rfl fun _ _ _ _ _ h _ => h, (hcl s c hi).2⟩⟩
    fun s c h => hKu s c h.1 h.2).mono_W (fun _ _ h => h.1) |>.seq
      ((SegW.exists_pre hC).mono_pre fun _ _ ⟨⟨g, h⟩, hu⟩ => ⟨g, h, hu⟩)
  refine ((Spike.Lib.A64.Flow.WakeWc.SegW.keepTPA hK hseg hKt).mono_pre fun _ _ ⟨⟨l, A, h, hQ⟩, hu, ht⟩ =>
    ⟨⟨⟨l, A, at_bXH_tpXa h, hQ⟩, hu⟩, ht⟩).mono_post ?_
  rintro s c ⟨⟨c0, sl, me, cA, fr, hM, hGm, hA⟩, ht⟩
  have hb := wcNSH_base hR (by omega) hhi hA
  obtain rfl : c = c0 := let ⟨_, _, _, _, _, _, _, hc, _⟩ := hA; hc
  exact ⟨sl, me, cA, fr, hM, hGm, hA, hb, ht⟩

end Seg

/-! ## The take of the second stack or a `clone` refusal -/

section Take

variable {L : RuntimeLayout} {R : Region} {a : Int64} {Cl : State → Prop}

/-- **`TakeCK` keeps `R`'s cells** when `R` ends below the second stack
(`R.hi ≤ 80`, `R`'s base 80 below the first stack's top: `BoxPureH`'s). -/
theorem takeCKH_kR (hR : R.OK) (hhi : R.hi ≤ 80) (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64) :
    ∀ s s', TakeCK a (r1Of L.lab) Cl s s' → ∀ k, R.Off k →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 := by
  intro s s' hk k hk'
  rcases hk with h | ⟨_, _, _, rfl⟩
  · obtain ⟨pm, he⟩ := h.mem
    rw [he]
    refine Ret0.loadInt_takeMem fun j hj hm => ?_
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
    have hx := List.mem_range.mp hx
    have ha := Region.addr_toNat hR hk'
    have hf8 := Region.addr_fit hR hk'
    have hl := Spike.Lib.A64.WakePh.Ti2.r1_lo (L := L)
    have hsz : (r1Of L.lab).size = 16384 := rfl
    have h1 := congrArg BitVec.toNat he
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)] at h1
    rw [Nat.mod_eq_of_lt (by omega : (R.addr k).toNat + j < 2 ^ 64)] at h1
    rw [Nat.mod_eq_of_lt (by omega : (r1Of L.lab).lo + x < 2 ^ 64)] at h1
    obtain ⟨-, -, h3⟩ := hk'
    omega
  · rfl

/-- **No write inside `R` breaks `StackM r1Of`**: `R` ends below the second
stack (`R.hi ≤ 80`, its base 80 below it). -/
theorem stackM_r1H (hhi : R.hi ≤ 80) (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64) : FStable R (StackM (r1Of L.lab)) :=
  Ret0.stackM_stable hfit1 fun _ _ ha _ => .inr (by
    have := Spike.Lib.A64.WakePh.Ti2.r1_lo (L := L)
    simp only [Scc.Sem.Range.contains] at ha; omega)

end Take

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcMidWH.antiF₂' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcMidWH.antiF₂

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_hatK' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_hatK

/-- info: 'Spike.Lib.A64.Flow.HelloWc.takeCKH_kR' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.takeCKH_kR

/-- info: 'Spike.Lib.A64.Flow.HelloWc.stackM_r1H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.stackM_r1H
