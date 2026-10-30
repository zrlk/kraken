/-
**`wake_wc_mid_hatW` under an outside move that moves the callee's states**
(AArch64, the pre-spawn consumer; `hatA`): the same end at main's parent
node, the segment (callee included) inside `W ∧ NoMsrAt` (`SegW.keepTPA`)
rather than `NoMsrW W K`, so `K` may move states inside `scc_rt_thread_init`
(its take), given that `K` keeps the thread pointer (`hKt`). The callee's
segment is asked at the ghosts' facts (`MidG`, `FrG`, `FrMG`).

- `wake_wc_mid_hatK`: `wake_wc_mid_segW`'s composite, its callee given the
  ghosts' facts, then `SegW.keepTPA` and `wc_mid_hat`;
- `WcMidW.antiF₂`: the node obligations at a stronger late frame condition;
- `takeCK_fK`, `takeCK_kR`, `takeCK_tp`, `stackM_r1`: the take of the second
  stack `r1Of` or a `clone` refusal (`TakeCK`) keeps a frame condition closed
  under `takeMem` and the memory, `R`'s cells below the second stack, and the
  thread pointer; no write inside `R` breaks `StackM r1Of`.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeWcHat
import Spike.Lib.A64WakeTi2Box
import Spike.Lib.A64SFactsAC
import Spike.Lib.A64KeepUn
import Spike.Lib.A64OwnedPz
import Spike.Lib.A64WakeWcK1

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.WcSp4 (wcNS wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW wcN3 tcb2Q)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX StackM)
open Spike.Lib.A64.Rt (TcbOkGA hdrA RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (NoMsrAt TP tpXa)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64ConsumerA (TakeCK)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.A64Consumer (Pz)

section Anti

variable {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F₂ F₂' : MachineData → Prop} (hf : ∀ m, F₂' m → F₂ m)
include hf

/-- **From the box's store to the `svc` at a stronger late frame condition**
(`F₂' ⊆ F₂`: fewer states at the nodes past the call). -/
theorem WcMidW.antiF₂ {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcMidW W K exe endPc R F F₂ ms J0 S Q) : WcMidW W K exe endPc R F F₂' ms J0 S Q := by
  have hb : ∀ {n blk}, BlkW W K exe endPc R F₂ n blk → BlkW W K exe endPc R F₂' n blk :=
    fun h s σ c he hn hd hpc hA hD hJ => h s σ c he hn hd hpc hA (hf _ hD) hJ
  have hn : ∀ {n}, NodeW W K exe endPc R F₂ n → NodeW W K exe endPc R F₂' n :=
    fun h s c ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hd, hpc, σ, hA, hf _ hD, hJ⟩
  exact ⟨h.res, h.sp3, fun c0 cA m fr hM => let h4 := h.sp4 c0 cA m fr hM
    ⟨h4.n4, h4.n4s, h4.n5, h4.nI, hb h4.n6, hn h4.n6f, hb h4.n6a⟩⟩

end Anti

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wake_wc_mid_hatW` inside `W ∧ NoMsrAt`**: its premises, the node
obligations (`hW`) and the callee (`hti`, given the ghosts' facts) inside
`W ∧ NoMsrAt` at `tpXa ms t`, under an outside move keeping the thread
pointer (`hKt`). The second stack `r1Of` is unmapped at the entry and kept
unmapped up to the call (`hKu` off the clone and the take site, `OffC`;
`KeepUn.SegW.keepUn`): the callee is promised `Pz r1Of` at its entry
(`wake_wc_sp4_call_segW`). -/
theorem wake_wc_mid_hatK {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hfit : (R.base.toNat : Int) + 16 ≤ 2 ^ 64)
    (hup : ∀ m, F₂ m → ∀ k : Int, k % 8 = 0 → 0 ≤ k → k < 16 → (Mem.loadInt m.dmem (R.addr k) 8).isSome)
    (hW : WcMidW (fun s c => W s c ∧ NoMsrAt s) K exe endPc R F F₂ (tpXa ms t) J0 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-80) (-192) 0) F (tcb2Q g c0))
    (htid : ms.rt (t2 (_root_.Executable.labels exe).label + 56#64).toNat ∧
      ms.mp ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ true ∧
      ms.G ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (_root_.Executable.labels exe).label + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-192) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hKt : ∀ s s', K s s' → TP t s → TP t s')
    (hKu : ∀ s c, W s c ∧ NoMsrAt s → OffC exe s c → ∀ s', K s s' →
      U (r1Of (_root_.Executable.labels exe).label) s → U (r1Of (_root_.Executable.labels exe).label) s')
    (hti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64), MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ (R' : Region) (F' : MachineData → Prop),
      R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-80) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J
            σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-80) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧
          (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-80) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => W s c ∧ NoMsrAt s) K p lbl (tpXa ms t)
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e) s c ∧
              Pz (r1Of (_root_.Executable.labels exe).label) s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) x) s c ∧ M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c) ∧
        U (r1Of (_root_.Executable.labels exe).label) s ∧ TP t s)
      (fun s c => ∃ cA m fr, MidG S c cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c (t2 (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) cA m fr) s c ∧
        (⟨R.base, -96, 16⟩ : Region).OK ∧ At exe endPc ⟨R.base, -96, 16⟩ F₂
          ⟨Spike.Lib.WakePreA.cloneAt pfxM exe, oP, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
        (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 80 ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have eW : SccCode.wakeProg = Spike.Lib.A64.WakeLabels.wakeProg := by decide +kernel
  have hWo := WcMidW.and hW (wcMidW_offC (eW ▸ hp))
  have hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-256) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
    fun s s' hk hD k hk' hn => hKR s s' hk hD k hk' fun ⟨h1, h2, h3⟩ =>
      hn ⟨h1, by simp only [Region.callee] at h2 ⊢; omega, by simp only [Region.callee] at h3 ⊢; omega⟩
  -- `wake_wc_mid_segW`'s composite to the call node, `r1Of` kept unmapped; then the call
  let NI : Ctl × BitVec 64 × BitVec 64 × (BitVec 64 × BitVec 64) → Frag isaLSE2 := fun g s c =>
    At exe endPc R F (wcNI lab g.1 (t2 lab) g.2.1 g.2.2.1 g.2.2.2) s c ∧
      (MidG S g.1 g.2.1 ∧ FrG J0 g.2.2.2 ∧ FrMG J0 g.2.2.2 g.2.2.1)
  have hG : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64),
      SegW (fun s c => (W s c ∧ NoMsrAt s) ∧ OffC exe s c) K p lbl (tpXa ms t)
        (fun s c => At exe endPc R F (wcN3 lab (j3 cA m fr) c0) s c ∧ (MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m))
        (fun s c => ∃ g, NI g s c) :=
    fun c0 cA m fr => SegW.of_imp fun hM =>
      ((wake_wc_sp3_segW hp hend hF hR hal (by omega) hhi (hWo.sp3 c0 cA m fr hM)
        (fun g => stOk_tpXa (hhdr c0 g)) (fun g => tcbOkGA_tpXa (htcb c0 g)) hFK hKR).seq
        (wake_wc_sp4_pre_segW hp hend hF hR hal hlo hhi (hWo.sp4 c0 cA m fr hM) htid)).mono_post
        fun _ _ h => ⟨(c0, cA, m, fr), h, hM⟩
  have hC : ∀ g, SegW (fun s c => W s c ∧ NoMsrAt s) K p lbl (tpXa ms t) (fun s c => NI g s c ∧ U (r1Of lab) s)
      (fun s c => ∃ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS lab c0 (t2 lab) (kOf lab) cA m fr) s c) := fun g =>
    (SegW.of_imp (P := At exe endPc R (fun m => F m ∧ Pz (r1Of lab) m) (wcNI lab g.1 (t2 lab) g.2.1 g.2.2.1 g.2.2.2))
      fun hM => (wake_wc_sp4_call_segW (P := Pz (r1Of lab)) hp hend hF hR hal hlo hhi hF₂s hF₂
        (hW.sp4 g.1 g.2.1 g.2.2.1 g.2.2.2 hM) hFK hKR4 (hti g.1 g.2.1 g.2.2.1 g.2.2.2 hM)).mono_post
        fun _ _ h => ⟨g.1, g.2.1, g.2.2.1, g.2.2.2, hM.1, hM.2.1, hM.2.2, h⟩).mono_pre
      fun _ _ ⟨⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩, hu⟩ =>
        ⟨⟨he, hn, hdc, hpc, σ, hA, ⟨hD, A64Consumer.pz_of_unowned (by show 0 < 16384; decide) hu.2⟩, hJ⟩, hM⟩
  obtain ⟨inv, hP, hiW, hcl⟩ := (wake_wc_res_segW hp hend hF hR hal (by omega) hhi hWo.res
    (fun q l A hQ => hfr ⟨q.1, okb_of_tpXa q.2⟩ l A hQ) fun g => resOkA_tpXa (hres g)).seq
    ((SegW.exists_pre (P := fun (g : Ctl × BitVec 64 × BitVec 64 × (BitVec 64 × BitVec 64)) s c =>
      At exe endPc R F (wcN3 lab (j3 g.2.1 g.2.2.1 g.2.2.2) g.1) s c ∧
        (MidG S g.1 g.2.1 ∧ FrG J0 g.2.2.2 ∧ FrMG J0 g.2.2.2 g.2.2.1))
      fun g => hG g.1 g.2.1 g.2.2.1 g.2.2.2).mono_pre fun s c ⟨x, h⟩ => by
        obtain ⟨cA, m, fr, hM, hG', hGm, h⟩ := rX_wcN3 h
        exact ⟨(c, cA, m, fr), h, hM, hG', hGm⟩)
  -- at `unXa` (`Out.mono_xa`), then `r1Of` kept unmapped to the call node
  have hseg := (A64.KeepUn.SegW.keepUn (r := r1Of lab) hK (ms := tpXa ms t) ⟨inv, hP, hiW, fun s c hi =>
    ⟨fun hk => A64ConsumerA.Out.mono_xa ((hcl s c hi).1 hk) rfl fun _ _ _ _ _ h _ => h, (hcl s c hi).2⟩⟩
    fun s c h => hKu s c h.1 h.2).mono_W (fun _ _ h => h.1) |>.seq
      ((SegW.exists_pre hC).mono_pre fun _ _ ⟨⟨g, h⟩, hu⟩ => ⟨g, h, hu⟩)
  refine ((SegW.keepTPA hK hseg hKt).mono_pre fun _ _ ⟨⟨l, A, h, hQ⟩, hu, ht⟩ =>
    ⟨⟨⟨l, A, at_bX_tpXa h, hQ⟩, hu⟩, ht⟩).mono_post ?_
  rintro s c ⟨⟨c0, cA, m, fr, hM, hG, hGm, hA⟩, ht⟩
  have hD : F₂ s.st.1 := let ⟨_, _, _, _, _, _, hD, _⟩ := hA; hD
  obtain ⟨rfl, hok, hat, hb⟩ := wc_mid_hat hR (by omega) hhi hfit (hup _ hD) hA ht
  exact ⟨cA, m, fr, hM, hG, hGm, hA, hok, hat, hb, ht⟩

end Seg

/-! ## The take of the second stack or a `clone` refusal -/

section Take

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {a : Int64} {Cl : State → Prop}

/-- **`TakeCK` keeps a frame condition** closed under the take of `r1Of`
(`hcl`) and determined by the memory (`hcg`; a refusal moves only `x0` and
the pc). -/
theorem takeCK_fK (hcl : ∀ m pm, F m → F (Ret0.takeMem pm (r1Of L.lab) m))
    (hcg : ∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m') : KStable (TakeCK a (r1Of L.lab) Cl) F :=
  fun s s' hk hm => hk.elim (fun h => Ret0.TakeK.kstable hcl s s' h hm)
    fun ⟨_, _, _, he⟩ => hcg _ _ (by subst he; rfl) hm

/-- **`TakeCK` keeps `R`'s cells** when `R` ends below the second stack
(`R.hi ≤ 48`, `R`'s base 48 below the first stack's top). -/
theorem takeCK_kR (hR : R.OK) (hhi : R.hi ≤ 48) (hb : R.base.toNat + 48 = L.stacksA.toNat + 16384)
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

/-- **`TakeCK` keeps the thread pointer.** -/
theorem takeCK_tp {rS : Scc.Sem.Range} {t : UInt64} :
    ∀ s s', TakeCK a rS Cl s s' → TP t s → TP t s' :=
  fun _ _ hk hs => hk.elim (fun h => takeK_tp h hs) fun ⟨_, _, _, he⟩ => by subst he; exact hs

/-- **No write inside `R` breaks `StackM r1Of`**: `R` ends below the second
stack. -/
theorem stackM_r1 (hhi : R.hi ≤ 48) (hb : R.base.toNat + 48 = L.stacksA.toNat + 16384)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64) : FStable R (StackM (r1Of L.lab)) :=
  Ret0.stackM_stable hfit1 fun _ _ ha _ => .inr (by
    have := Spike.Lib.A64.WakePh.Ti2.r1_lo (L := L)
    simp only [Scc.Sem.Range.contains] at ha; omega)

end Take

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcMidW.antiF₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcMidW.antiF₂

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_hatK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_hatK

/-- info: 'Spike.Lib.A64.Flow.WakeWc.takeCK_fK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.takeCK_fK

/-- info: 'Spike.Lib.A64.Flow.WakeWc.takeCK_kR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.takeCK_kR

/-- info: 'Spike.Lib.A64.Flow.WakeWc.takeCK_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.takeCK_tp

/-- info: 'Spike.Lib.A64.Flow.WakeWc.stackM_r1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.stackM_r1
