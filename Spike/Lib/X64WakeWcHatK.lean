/-
**`wake_wc_mid_hatW` under an outside move that moves the callee's states**
(x86-64; the twin of `Spike/Lib/A64WakeWcHatK.lean`): the same end at
main's parent node, the segment (callee included) inside `W ∧ NoSetFsAt`
(`SegW.keepTPA`) rather than `NoSetFsW W K`, so `K` may move states inside
`scc_rt_thread_init` (its take), given that `K` keeps the thread pointer
(`hKt`). The callee's segment is asked at the ghosts' facts (`MidG`, `FrG`,
`FrMG`).

- `wake_wc_mid_hatK`: `wake_wc_mid_segW`'s composite, its callee given the
  ghosts' facts, then `SegW.keepTPA` and `wc_mid_hat`;
- `WcMidW.antiF₂`: the node obligations at a stronger late frame condition;
- `takeCK_fK`, `takeCK_kR`, `takeCK_tp`, `stackM_r1`: the take of the second
  stack `r1Of` or a `clone` refusal (`TakeCK`) keeps a frame condition closed
  under `takeMem` and the memory, `R`'s cells below the second stack, and the
  thread pointer; no write inside `R` breaks `StackM r1Of`.

**Where this differs from AArch64**: the source is published at
`wc_main`'s `mfence` past the callee (`X64WakeWcPub`), so the composite is
`wake_wc_sp4_pre_segW` to the call node, `wake_wc_sp4_ret_segW` (the callee
promised `Pz r1Of`) to `.x21`, then `wake_wc_clone_pub_segW`; the exit is at
the published control `boxPubCtl c0 ty l` with `MidPG` (`hpub`, `hP` in place
of A64's `hfr`); the frame offsets are x86-64's (`[-320, 16)`, the callee at
`-72`, A64's `[-336, 0)` at `-80`); no alignment premise; `R`'s end below the
second stack is a parameter `d` (A64's `48`). No absolute address appears in
this file.
-/
import Spike.Lib.X64WakeWcHat
import Spike.Lib.X64WakeTi2Box
import Spike.Lib.X64SFactsAC
import Spike.Lib.X64KeepUn
import Spike.Lib.X64OwnedPz
import Spike.Lib.X64WakeWcK1

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Tcb2Call (oC wcN3 tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk StackM)
open Spike.Lib.X64.Rt (TcbOkGA hdrA RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ResOkA)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64WakeBoxDefs (boxTerm boxPubCtl)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64ConsumerA (TakeCK)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64Consumer (Pz)
open Scc.Cert.Rt.X64 (Lays endOf)

section Anti

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F₂ F₂' : MachineData → Prop} (hf : ∀ m, F₂' m → F₂ m)
include hf

/-- **From the box's store to the `syscall` at a stronger late frame
condition** (`F₂' ⊆ F₂`: fewer states at the nodes past the call). -/
theorem WcMidW.antiF₂ {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcMidW W K exe endPc R F F₂ ms J0 Q) : WcMidW W K exe endPc R F F₂' ms J0 Q := by
  have hb : ∀ {n blk}, BlkW W K exe endPc R F₂ n blk → BlkW W K exe endPc R F₂' n blk :=
    fun h s σ c he hn hd hpc hA hD hJ => h s σ c he hn hd hpc hA (hf _ hD) hJ
  have hn : ∀ {n}, NodeW W K exe endPc R F₂ n → NodeW W K exe endPc R F₂' n :=
    fun h s c ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hd, hpc, σ, hA, hf _ hD, hJ⟩
  exact ⟨h.res, h.sp3, fun c0 ty l cA m fr hM => let h4 := h.sp4 c0 ty l cA m fr hM
    ⟨h4.toWcSp4PreW, ⟨hb h4.clone.n21, hn h4.clone.nf, hb h4.clone.na, hn h4.clone.nd, hn h4.clone.n10,
      hb h4.clone.nr⟩⟩⟩

end Anti

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wake_wc_mid_hatW` inside `W ∧ NoSetFsAt`**: its premises, the node
obligations (`hW`) and the callee (`hti`, given the ghosts' facts) inside
`W ∧ NoSetFsAt` at `tpXa ms t`, under an outside move keeping the thread
pointer (`hKt`). The second stack `r1Of` is unmapped at the entry and kept
unmapped up to the call (`hKu` off the clone, `OffC`;
`KeepUn.SegW.keepUn`): the callee is promised `Pz r1Of` at its entry
(`wake_wc_sp4_ret_segW`). -/
theorem wake_wc_mid_hatK {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcMidW (fun s c => W s c ∧ NoSetFsAt s) K exe endPc R F F₂ (tpXa ms t) J0 Q)
    (hpub : ∀ l A c, Q l A c → c.term = boxTerm ∧ c.hold = none ∧
      ∃ ty, TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hP : ms.pub)
    (hres : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, StOk ms F (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-72) (-184) 8) F (tcb2Q g c0))
    (htid : ms.rt (t2 (_root_.Executable.labels exe).label + 56#64).toNat ∧
      ms.mp ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ true ∧
      ms.G ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (_root_.Executable.labels exe).label + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-184) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hKt : ∀ s s', K s s' → TP t s → TP t s')
    (hKu : ∀ s c, W s c ∧ NoSetFsAt s → OffC exe s c → ∀ s', K s s' →
      U (r1Of (_root_.Executable.labels exe).label) s → U (r1Of (_root_.Executable.labels exe).label) s')
    (hti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64), MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
      ∀ (R' : Region) (F' : MachineData → Prop),
      R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J
            σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧
          (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => W s c ∧ NoSetFsAt s) K p lbl (tpXa ms t)
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e) s c ∧
              Pz (r1Of (_root_.Executable.labels exe).label) s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) x) s c ∧ M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c) ∧
        U (r1Of (_root_.Executable.labels exe).label) s ∧ TP t s)
      (fun s c => ∃ c0 ty l cA m fr, c = boxPubCtl c0 ty l ∧ MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c
          (t2 (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label) cA m fr) s c ∧
        (⟨R.base, -64, 16⟩ : Region).OK ∧
        At exe endPc ⟨R.base, -64, 16⟩ F₂ ⟨cloneAt exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
        (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64 ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hWo := WcMidW.and hW (wcMidW_offC hp)
  have hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-248) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
    fun s s' hk hD k hk' hn => hKR s s' hk hD k hk' fun ⟨h1, h2, h3⟩ =>
      hn ⟨h1, by simp only [Region.callee] at h2 ⊢; omega, by simp only [Region.callee] at h3 ⊢; omega⟩
  -- the ghost at the call node: the source, its publication's type and label, the frame's words
  let GG := Ctl × Ty × WeakMem.AllocLabel × BitVec 64 × BitVec 64 × (BitVec 64 × BitVec 64)
  let NI : GG → Frag isa := fun g s c =>
    At exe endPc R F (wcNI lab g.1 (t2 lab) g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2) s c ∧
      (MidPG Q g.1 g.2.1 g.2.2.1 g.2.2.2.1 ∧ MidG Q g.1 g.2.2.2.1 ∧ FrG J0 g.2.2.2.2.2 ∧
        FrMG J0 g.2.2.2.2.2 g.2.2.2.2.1)
  -- `.x19` to the call node, off the clone's pc
  have hG : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64),
      SegW (fun s c => (W s c ∧ NoSetFsAt s) ∧ OffC exe s c) K p lbl (tpXa ms t)
        (fun s c => At exe endPc R F (wcN3 lab (j3 cA m fr) c0) s c ∧ (MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m))
        (fun s c => ∃ g, NI g s c) := by
    refine fun c0 cA m fr => SegW.of_imp fun hM => ?_
    obtain ⟨⟨l, A, hQ, hA⟩, hG, hGm⟩ := hM
    obtain ⟨ht, hh, ty, ho⟩ := hpub l A c0 hQ
    have hMP : MidPG Q c0 ty l cA := ⟨hA ▸ hQ, ht, hh, ho⟩
    exact ((wake_wc_sp3_segW hp hend hF hR (by omega) hhi (hWo.sp3 c0 cA m fr ⟨⟨l, A, hQ, hA⟩, hG, hGm⟩)
      (fun g => stOk_tpXa (hhdr c0 g)) (fun g => tcbOkGA_tpXa (htcb c0 g)) hFK hKR).seq
      (wake_wc_sp4_pre_segW hp hend hF hR (by omega) hhi (hWo.sp4 c0 ty l cA m fr ⟨hMP, hG, hGm⟩).toWcSp4PreW
        htid)).mono_post
      fun _ _ h => ⟨(c0, ty, l, cA, m, fr), h, hMP, ⟨l, A, hQ, hA⟩, hG, hGm⟩
  -- the call to the `syscall`, the callee promised `Pz r1Of`
  have hC : ∀ g : GG, SegW (fun s c => W s c ∧ NoSetFsAt s) K p lbl (tpXa ms t)
      (fun s c => NI g s c ∧ U (r1Of lab) s)
      (fun s c => ∃ c0 ty l cA m fr, MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS lab (boxPubCtl c0 ty l) (t2 lab) (kOf lab) cA m fr) s c) := fun g =>
    (SegW.of_imp (P := At exe endPc R (fun m => F m ∧ Pz (r1Of lab) m)
        (wcNI lab g.1 (t2 lab) g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2))
      fun hM => ((wake_wc_sp4_ret_segW (P := Pz (r1Of lab)) hF hR hlo hhi hF₂ hFK hKR4
          (hti g.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 hM.2)).seq
        (wake_wc_clone_pub_segW hp hend WakePh.wake_wcCloneIn hF₂s hR (by omega) hhi hM.1.2.1 hM.1.2.2.1
          hM.1.2.2.2 hP (hW.sp4 g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2
            ⟨hM.1, hM.2.2⟩).clone)).mono_post
        fun _ _ h => ⟨g.1, g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2, hM.1, hM.2.2.1, hM.2.2.2, h⟩).mono_pre
      fun _ _ ⟨⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩, hu⟩ =>
        ⟨⟨he, hn, hdc, hpc, σ, hA, ⟨hD, Spike.Lib.X64Consumer.pz_of_unowned (by show 0 < 16384; decide) hu.2⟩,
          hJ⟩, hM⟩
  obtain ⟨inv, hP0, hiW, hcl⟩ := (wake_wc_res_segW hp hend hF hR (by omega) hhi hWo.res
    fun g => resOkA_tpXa (hres g)).seq
    ((SegW.exists_pre (P := fun (g : Ctl × BitVec 64 × BitVec 64 × (BitVec 64 × BitVec 64)) s c =>
      At exe endPc R F (wcN3 lab (j3 g.2.1 g.2.2.1 g.2.2.2) g.1) s c ∧
        (MidG Q g.1 g.2.1 ∧ FrG J0 g.2.2.2 ∧ FrMG J0 g.2.2.2 g.2.2.1))
      fun g => hG g.1 g.2.1 g.2.2.1 g.2.2.2).mono_pre fun s c ⟨x, h⟩ => by
        obtain ⟨cA, m, fr, hM, hG', hGm, h⟩ := rX_wcN3 h
        exact ⟨(c, cA, m, fr), h, hM, hG', hGm⟩)
  -- at `unXa` (`Out.mono_xa`), then `r1Of` kept unmapped to the call node
  have hseg := (Spike.Lib.X64.KeepUn.SegW.keepUn (r := r1Of lab) hK (ms := tpXa ms t) ⟨inv, hP0, hiW,
    fun s c hi => ⟨fun hk => Spike.Lib.X64ConsumerA.Out.mono_xa ((hcl s c hi).1 hk) rfl
      fun _ _ _ _ _ h _ => h, (hcl s c hi).2⟩⟩
    fun s c h => hKu s c h.1 h.2).mono_W (fun _ _ h => h.1) |>.seq
      ((SegW.exists_pre hC).mono_pre fun _ _ ⟨⟨g, h⟩, hu⟩ => ⟨g, h, hu⟩)
  refine ((SegW.keepTPA hK hseg hKt).mono_pre fun _ _ ⟨⟨l, A, h, hQ⟩, hu, ht⟩ =>
    ⟨⟨⟨l, A, at_bX_tpXa h, hQ⟩, hu⟩, ht⟩).mono_post ?_
  rintro s c ⟨⟨c0, ty, l, cA, m, fr, hM, hG, hGm, hA⟩, ht⟩
  obtain ⟨rfl, hok, hat, hb⟩ := wc_mid_hat hR (by omega) hhi hA ht
  exact ⟨c0, ty, l, cA, m, fr, rfl, hM, hG, hGm, hA, hok, hat, hb, ht⟩

end Seg

/-! ## The take of the second stack or a `clone` refusal -/

section Take

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {a : Int64} {Cl : State → Prop}

/-- **`TakeCK` keeps a frame condition** closed under the take of `r1Of`
(`hcl`) and determined by the memory (`hcg`; a refusal moves only `%rax`
and the pc). -/
theorem takeCK_fK (hcl : ∀ m pm, F m → F (Ret0.takeMem pm (r1Of L.lab) m))
    (hcg : ∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m') : KStable (TakeCK a (r1Of L.lab) Cl) F :=
  fun s s' hk hm => hk.elim (fun h => Ret0.TakeK.kstable hcl s s' h hm)
    fun ⟨_, _, _, he⟩ => hcg _ _ (by subst he; rfl) hm

/-- **`TakeCK` keeps `R`'s cells** when `R` ends `d` above its base, at or
below the second stack (`R`'s base `d` below the first stack's top). -/
theorem takeCK_kR {d : Nat} (hR : R.OK) (hhi : R.hi ≤ d) (hb : R.base.toNat + d = L.stacksA.toNat + 16384)
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
    have hl := Spike.Lib.X64.WakePh.Ti2.r1_lo (L := L)
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

/-- **No write inside `R` breaks `StackM r1Of`**: `R` ends at or below the
second stack. -/
theorem stackM_r1 {d : Nat} (hhi : R.hi ≤ d) (hb : R.base.toNat + d = L.stacksA.toNat + 16384)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64) : FStable R (StackM (r1Of L.lab)) :=
  Ret0.stackM_stable hfit1 fun _ _ ha _ => .inr (by
    have := Spike.Lib.X64.WakePh.Ti2.r1_lo (L := L)
    simp only [Scc.Sem.Range.contains] at ha; omega)

end Take

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcMidW.antiF₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcMidW.antiF₂

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_hatK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_hatK

/-- info: 'Spike.Lib.X64.Flow.WakeWc.takeCK_fK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.takeCK_fK

/-- info: 'Spike.Lib.X64.Flow.WakeWc.takeCK_kR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.takeCK_kR

/-- info: 'Spike.Lib.X64.Flow.WakeWc.takeCK_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.takeCK_tp

/-- info: 'Spike.Lib.X64.Flow.WakeWc.stackM_r1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.stackM_r1
