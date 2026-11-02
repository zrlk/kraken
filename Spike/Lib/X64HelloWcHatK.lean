/-
**hello.w's `wc_main` from the box's store to the `clone` under an outside move that moves the callee's states**
(x86-64; the twin of `Spike/Lib/A64HelloWcHatK.lean`, wake's x86-64 `Spike/Lib/X64WakeWcHatK.lean` at hello's
`wc_main`, frame 128): the segment (callee included) inside `W ∧ NoSetFsAt` (`SegW.keepTPA`) rather than
`NoSetFsW W K`, so `K` may move states inside `scc_rt_thread_init` (its take), given that `K` keeps the thread
pointer (`hKt`). The callee's segment is asked at the ghosts' facts (`MidG`, `FrMGH`) with the second stack `r1Of`
unmapped at its entry (`Pz r1Of`).

Reused from wake as is (layout generic): `takeCK_fK`, `takeCK_tp`, `SegW.keepTPA`, `KeepUn.SegW.keepUn`.

- `WcMidWH.antiF₂`: the node obligations at a stronger late frame condition;
- `hello_wc_mid_hatK`: the composite (`hello_wc_res_segW`, `hello_wc_sp3_segW`, `hello_wc_sp4_pre_segW`,
  `hello_wc_sp4_call_segW`, `hello_wc_sp6_pub_segW`), `r1Of` kept unmapped up to the call (`KeepUn.SegW.keepUn`,
  off the clone's and the take site's pcs: `OffCH`), its callee given the ghosts' facts, the box published at
  `.x25`'s `mfence` (`hpub`, `hP`), then `SegW.keepTPA` and `wcNSH_base`;
- `takeCKH_kR`, `stackM_r1H`: the take of `r1Of` or a `clone` refusal keeps `R`'s cells when `R` ends below the
  second stack (`R.hi ≤ 96`, `R`'s base 96 below it: `ClonePostH`'s `%rsp + 128` and `%rsp + 224`); no write
  inside such an `R` breaks `StackM r1Of` (wake's `takeCK_kR`, `stackM_r1` at `d = 96`).

No absolute address appears in this file.

## Differences from the AArch64 version

- The thread pointer is `fsBase`: `NoMsrAt` is `NoSetFsAt`, and the composite asks `ms.K = some X64.abi` (`hK`).
- The source takes no step at a fence past the box's store (x86-64's listing has none there), so there is no `hfr`
  and no `S`: the ghosts' guard up to `.x25` is `MidG Q`. The publication is at `.x25`'s `mfence`
  (`X64HelloWcPub.hello_wc_sp6_pub_segW`, as wake's x86-64 `wake_wc_mid_segW`): the source under `Q` is at
  `boxTermH` with no hold and `o` the box's owned locative (`hpub`), the memory side admits it (`hP`), and the exit
  is at the published control `boxPubCtlH c0 ty l` with `MidPGH Q c0 ty l cA`.
- The frame offsets are x86-64's: `R.lo ≤ -384`, `16 ≤ R.hi`, the callees at `-136` (`rARH R`,
  `R.callee (-136) (-184) 8`, `R.callee (-136) (-248) 8`), the exit's base `%rsp + 128`; no alignment premise.
- `R`'s end below the second stack is `96` (AArch64 `80`), and `takeCKH_kR`, `stackM_r1H` are wake's x86-64
  `takeCK_kR`, `stackM_r1` at `d = 96`.
-/
import Spike.Lib.X64HelloWcHat
import Spike.Lib.X64HelloWcK1
import Spike.Lib.X64HelloWcNoMsr
import Spike.Lib.X64WakeWcHatK

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk StackM)
open Spike.Lib.X64.HelloPh.WcSp6 (oWH wcNSH hello_wc_sp6_pub_segW MidPGH boxPubSyH)
open Spike.Lib.X64HelloMainPreSrc (boxTermH boxPubCtlH)
open Spike.Lib.X64.Flow.WakeWc (MidG kOf tiQ stOk_tpXa tcbOkGA_tpXa resOkA_tpXa takeCK_kR stackM_r1)
open Spike.Lib.X64.Rt (TcbOkGA hdrA RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ResOkA)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)
open Spike.Lib.X64ConsumerA (TakeCK)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64Consumer (Pz)

section Anti

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F₂ F₂' : MachineData → Prop} (hf : ∀ m, F₂' m → F₂ m)
include hf

/-- **From the box's store to the `syscall` at a stronger late frame condition** (`F₂' ⊆ F₂`: fewer states at
`.x25`'s nodes). -/
theorem WcMidWH.antiF₂ {ms : MemSide isa} {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcMidWH W K exe endPc R F F₂ ms J1 Q) : WcMidWH W K exe endPc R F F₂' ms J1 Q := by
  have hb : ∀ {n blk}, BlkW W K exe endPc R F₂ n blk → BlkW W K exe endPc R F₂' n blk :=
    fun h s σ c he hn hd hpc hA hD hJ => h s σ c he hn hd hpc hA (hf _ hD) hJ
  have hn : ∀ {n}, NodeW W K exe endPc R F₂ n → NodeW W K exe endPc R F₂' n :=
    fun h s c ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hd, hpc, σ, hA, hf _ hD, hJ⟩
  exact ⟨h.res, h.sp3, h.sp4, fun c0 ty l sl me cA fr hM => let h6 := h.sp6 c0 ty l sl me cA fr hM
    ⟨hb h6.n6, hn h6.n6f, hb h6.n6a, hn h6.nd, hn h6.n10, hb h6.nr⟩⟩

end Anti

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

set_option maxHeartbeats 1600000 in
/-- **`wc_main` from the box's store to the `clone` inside `W ∧ NoSetFsAt`**: the node obligations at
`tpXa ms t` inside `W ∧ NoSetFsAt` (`hW`); `scc_rt_thread_init` (`hti`) at the ghosts' facts with `r1Of`
unmapped at its entry, its states inside `W ∧ NoSetFsAt`; `K` keeps the thread pointer (`hKt`) and, off the
clone's and the take site's pcs, `r1Of` unmapped (`hKu`). From the box's landing with `r1Of` unmapped and the
thread pointer `t`, the segment ends inside `W` under `ms` at `wcNSH` with the source published at `.x25`'s
`mfence` (`hpub`, `hP`: `c = boxPubCtlH c0 ty l`, `MidPGH`, `FrMGH` at its ghosts), the base `%rsp + 128`,
`TP t`. -/
theorem hello_wc_mid_hatK {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -384) (hhi : 16 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcMidWH (fun s c => W s c ∧ NoSetFsAt s) K exe endPc R F F₂ (tpXa ms t) J1 Q)
    (hpub : ∀ l A c, Q l A c → c.term = boxTermH ∧ c.hold = none ∧
      ∃ ty, TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hP : ms.pub)
    (hres : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms F exe endPc (rARH R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, StOk ms F (hdrA (_root_.Executable.labels exe).label (tcb2QH g c0))
      ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0))
    (htid : ms.rt (tH (_root_.Executable.labels exe).label + 56#64).toNat ∧
      ms.mp ⟨tH (_root_.Executable.labels exe).label + 56#64, 8⟩ true ∧
      ms.G ⟨tH (_root_.Executable.labels exe).label + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (tH (_root_.Executable.labels exe).label + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-136) (-184) 8).Off (k - -136) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hKt : ∀ s s', K s s' → TP t s → TP t s')
    (hKu : ∀ s c, W s c ∧ NoSetFsAt s → OffCH exe s c → ∀ s', K s s' →
      U (r1Of (_root_.Executable.labels exe).label) s → U (r1Of (_root_.Executable.labels exe).label) s')
    (hti : ∀ c0 sl me cA fr, MidG Q c0 cA ∧ FrMGH J1 fr sl me →
      ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-136) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -136) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 (tH (_root_.Executable.labels exe).label)
            sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (tH (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-136) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oCH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 (tH (_root_.Executable.labels exe).label)
            sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (tH (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-136) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -136) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => W s c ∧ NoSetFsAt s) K p lbl (tpXa ms t)
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label
            (tiQ (tH (_root_.Executable.labels exe).label) c0 g) .e) s c ∧
              Pz (r1Of (_root_.Executable.labels exe).label) s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label
            (tiQ (tH (_root_.Executable.labels exe).label) c0 g) x) s c ∧ M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c ∧ Q l A c) ∧
        U (r1Of (_root_.Executable.labels exe).label) s ∧ TP t s)
      (fun s c => ∃ c0 ty l sl me cA fr, c = boxPubCtlH c0 ty l ∧ MidPGH Q c0 ty l cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH (_root_.Executable.labels exe).label (boxPubCtlH c0 ty l)
          (tH (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label) sl me cA fr) s c ∧
        (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 128 ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hWo := WcMidWH.and hW (wcMidW_offCH hp)
  have hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-136) (-248) 8).Off (k - -136) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
    fun s s' hk hD k hk' hn => hKR s s' hk hD k hk' fun ⟨h1, h2, h3⟩ =>
      hn ⟨h1, by simp only [Region.callee] at h2 ⊢; omega, by simp only [Region.callee] at h3 ⊢; omega⟩
  -- the ghost at the call node: the source, the frame's words
  let NI : Ctl × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × BitVec 64 × BitVec 64 ×
      (BitVec 64 × BitVec 64) → Frag isa := fun g s c =>
    At exe endPc R F (wcNIH lab g.1 (tH lab) g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2) s c ∧
      (MidG Q g.1 g.2.2.2.1 ∧ FrMGH J1 g.2.2.2.2 g.2.1 g.2.2.1)
  -- `.x23` to the call node, off the clone's pc
  have hG : ∀ (c0 : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64)
      (fr : BitVec 64 × BitVec 64),
      SegW (fun s c => (W s c ∧ NoSetFsAt s) ∧ OffCH exe s c) K p lbl (tpXa ms t)
        (fun s c => At exe endPc R F (wcN3H lab c0 sl me cA fr) s c ∧ (MidG Q c0 cA ∧ FrMGH J1 fr sl me))
        (fun s c => ∃ g, NI g s c) :=
    fun c0 sl me cA fr => SegW.of_imp fun hM =>
      ((hello_wc_sp3_segW hp hend hF hR (by omega) hhi (hWo.sp3 c0 sl me cA fr hM)
        (fun g => stOk_tpXa (hhdr c0 g)) (fun g => tcbOkGA_tpXa (htcb c0 g)) hFK hKR).seq
        (hello_wc_sp4_pre_segW hp hend hF hR (by omega) hhi (hWo.sp4 c0 sl me cA fr hM) htid)).mono_post
        fun _ _ h => ⟨(c0, sl, me, cA, fr), h, hM⟩
  -- the call to the `syscall`, the callee promised `Pz r1Of`
  have hC : ∀ g, SegW (fun s c => W s c ∧ NoSetFsAt s) K p lbl (tpXa ms t) (fun s c => NI g s c ∧ U (r1Of lab) s)
      (fun s c => ∃ c0 ty l sl me cA fr, MidPGH Q c0 ty l cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH lab (boxPubCtlH c0 ty l) (tH lab) (kOf lab) sl me cA fr) s c) := fun g =>
    (SegW.of_imp (P := At exe endPc R (fun m => F m ∧ Pz (r1Of lab) m)
        (wcNIH lab g.1 (tH lab) g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2))
      fun hM => by
        obtain ⟨l, A, hQ, hcA⟩ := hM.1
        obtain ⟨ht, hh, ty, ho⟩ := hpub l A g.1 hQ
        have hPG : MidPGH Q g.1 ty l g.2.2.2.1 := ⟨hcA ▸ hQ, ht, hh, ho⟩
        exact ((hello_wc_sp4_call_segW (P := Pz (r1Of lab)) hF hR hlo hhi hF₂ hFK hKR4
          (hti g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 hM)).seq
          (hello_wc_sp6_pub_segW hp hend hF₂s hR (by omega) hhi (boxPubSyH ht hh ho) hP
            (hW.sp6 g.1 ty l g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 ⟨hPG, hM.2⟩))).mono_post
          fun _ _ h => ⟨g.1, ty, l, g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2, hPG, hM.2, h⟩).mono_pre
      fun _ _ ⟨⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩, hu⟩ =>
        ⟨⟨he, hn, hdc, hpc, σ, hA, ⟨hD, Spike.Lib.X64Consumer.pz_of_unowned (by show 0 < 16384; decide) hu.2⟩,
          hJ⟩, hM⟩
  obtain ⟨inv, hP0, hiW, hcl⟩ := (hello_wc_res_segW hp hend hF hR (by omega) hhi hWo.res
    fun g => resOkA_tpXa (hres g)).seq
    ((SegW.exists_pre (P := fun (g : Ctl × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) × BitVec 64 ×
        BitVec 64 × (BitVec 64 × BitVec 64)) s c =>
      At exe endPc R F (wcN3H lab g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2) s c ∧
        (MidG Q g.1 g.2.2.2.1 ∧ FrMGH J1 g.2.2.2.2 g.2.1 g.2.2.1))
      fun g => hG g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).mono_pre fun s c ⟨x, h⟩ => by
        obtain ⟨sl, me, cA, fr, hM, hGm, h⟩ := rXH_wcN3H h
        exact ⟨(c, sl, me, cA, fr), h, hM, hGm⟩)
  -- at `unXa` (`Out.mono_xa`), then `r1Of` kept unmapped to the call node
  have hseg := (Spike.Lib.X64.KeepUn.SegW.keepUn (r := r1Of lab) hK (ms := tpXa ms t) ⟨inv, hP0, hiW,
    fun s c hi => ⟨fun hk => Spike.Lib.X64ConsumerA.Out.mono_xa ((hcl s c hi).1 hk) rfl
      fun _ _ _ _ _ h _ => h, (hcl s c hi).2⟩⟩
    fun s c h => hKu s c h.1 h.2).mono_W (fun _ _ h => h.1) |>.seq
      ((SegW.exists_pre hC).mono_pre fun _ _ ⟨⟨g, h⟩, hu⟩ => ⟨g, h, hu⟩)
  refine ((Spike.Lib.X64.Flow.WakeWc.SegW.keepTPA hK hseg hKt).mono_pre fun _ _ ⟨⟨l, A, h, hQ⟩, hu, ht⟩ =>
    ⟨⟨⟨l, A, at_bXH_tpXa h, hQ⟩, hu⟩, ht⟩).mono_post ?_
  rintro s c ⟨⟨c0, ty, l, sl, me, cA, fr, hM, hGm, hA⟩, ht⟩
  have hb := wcNSH_base hR (by omega) (by omega) hA
  have hc : c = boxPubCtlH c0 ty l := by
    obtain ⟨-, -, -, -, -, -, -, ⟨⟨⟨hc, -⟩, -⟩, -⟩⟩ := hA
    exact hc
  exact ⟨c0, ty, l, sl, me, cA, fr, hc, hM, hGm, hA, hb, ht⟩

end Seg

/-! ## The take of the second stack or a `clone` refusal -/

section Take

variable {L : RuntimeLayout} {R : Region} {a : Int64} {Cl : State → Prop}

/-- **`TakeCK` keeps `R`'s cells** when `R` ends below the second stack (`R.hi ≤ 96`, `R`'s base 96 below the
first stack's top: `wc_main`'s at the clone). -/
theorem takeCKH_kR (hR : R.OK) (hhi : R.hi ≤ 96) (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64) :
    ∀ s s', TakeCK a (r1Of L.lab) Cl s s' → ∀ k, R.Off k →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
  takeCK_kR hR hhi hb hfit1

/-- **No write inside `R` breaks `StackM r1Of`**: `R` ends below the second stack (`R.hi ≤ 96`, its base 96 below
it). -/
theorem stackM_r1H (hhi : R.hi ≤ 96) (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64) : FStable R (StackM (r1Of L.lab)) :=
  stackM_r1 hhi hb hfit1

end Take

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcMidWH.antiF₂' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcMidWH.antiF₂

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_mid_hatK' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_mid_hatK

/-- info: 'Spike.Lib.X64.Flow.HelloWc.takeCKH_kR' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.takeCKH_kR

/-- info: 'Spike.Lib.X64.Flow.HelloWc.stackM_r1H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.stackM_r1H
