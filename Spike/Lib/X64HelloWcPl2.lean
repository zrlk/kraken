/-
**hello.w's `wc_main` own nodes placed at its slots** (x86-64; the twin of `Spike/Lib/A64HelloWcPl2.lean`):
`WcMainWH` at `PlacedSE … []`, the `hpl` premise of `WcW2.wcWf_W2H`, from main's source placed wherever
`wc_main`'s five slots read the cell, main's word and the slice (`SpawnPl.placedSE_boxSlotsH` before the
publication, `placedSE_pubSlotsH` past it).

- `placedSE_pubAtH`, `placedSE_pubSlotsH`: main's source past the publication (`boxPubCtlH c0 ty l`) placed at
  any five places; at `wc_main`'s slots.
- `hplP_GJ1H`: the same at a ghost of `GJ1H` (`SpawnPl.hplQ_GJ1H`'s twin past the publication).
- `PlH`: a node's states placed wherever the five slots read its abstract state's words.
- `nodeW_plH`, `blkW_plH`: a node and a block keeping the five slots inside `PlacedSE`.
- `KeepsH`, `keepsH_*`: `wc_main`'s blocks keep the five slots.
- `plH_mid`, `plH_pub`: a node before (after) the publication placed at the slots.
- `wcMainW_plH`: `WcMainWH` at `PlacedSE` from the two placements at the slots (`HsQ`, `HsP`).
- `wcMainW_plGJ1H`: the same at a ghost of `GJ1H` (`hpl`'s instance for `WcW2.wcWf_W2H`).

No absolute address appears in this file.

## Differences from the AArch64 version

- The five slots are `wc_main`'s spills from `%rbp`: the cell at `-48`, main's word at `-40`, the slice at `-8`,
  `-24`, `-32` (AArch64: `-104`, `-112`, `-144`, `-128`, `-120`); the bounds are `R.lo ≤ -48`, `0 ≤ R.hi`
  (AArch64 `-144`). `slots_absH` is `Wcl2.slots_absH` (on AArch64 it lives here and `Wcl2` imports it).
- x86-64's `WcMainWH` has four fields and the one source guard `QBH` (AArch64: a fence node and `SBH` with
  `QBH`), and `.x25`'s nodes past its `mfence` stand at the published control `boxPubCtlH c0 ty l`, so the second
  placement `HsP` is at that control (`placedSE_pubAtH`, `hplP_GJ1H`, new; AArch64's `Hs` is at `SBH`).
- Blocks are lists of `(Directive × Nat)` (`WakeSrcCtl.keepsSlot` over them); `.x25`'s blocks are `sp6AH`,
  `cloneLdH`, `nrB` and its single nodes the `mfence` and the two `xorl`s (AArch64: `sp6AH`, the fence,
  `cloneArgsH`).
-/
import Spike.Lib.X64HelloWcl2
import Spike.Lib.X64HelloWcW1

namespace Spike.Lib.X64.HelloPh.WcPl2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region Ctl)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64HelloMainPreSrc (SlRep boxPubCtlH)
open Spike.Lib.X64HelloHMid (QBH slWsH)
open Spike.Lib.X64.Flow.WakeWc (MidG)
open Spike.Lib.X64.Flow.HelloWc (WcMainWH FrMGH rNH wcN3H aNH resBH tcb2CallH sp4AH initCallH)
open Spike.Lib.X64.HelloPh.WcSp6 (FrWH MidPGH oWH sp6AH cloneLdH)
open Spike.Lib.X64.HelloPh.Ti2 (SlotPH SlotSlH slotRdH_place)
open Spike.Lib.X64.HelloPh.Wcl2 (slots_absH)
open Spike.Lib.X64.WakeSrcCtl (keepsSlot arun_slot_keep placedSE_of_tbl rep_at)

/-! ## main's source past the publication -/

/-- **main's source past the publication placed at any five places**: at `boxPubCtlH c0 ty l`, `c` at `pc`,
`me` at `pm`, `sl` at `pb`, `p2`, `p3` (the slice's words `w0`, `w1`, `w2`), given each place represents its word
(`lbl` puts `l` at `pc`'s word and main's id at `pm`'s). -/
theorem placedSE_pubAtH {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel}
    {w0 w1 w2 : TermRun.Word} (pb p2 p3 pc pm : Place (machine (kernel 1)).I.RegId)
    (hme : TermRun.evalAt c0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (hsl : TermRun.evalAt c0.env (.var "sl") = some (Spike.Lib.X64HelloSplit.slTy, [w0, w1, w2]))
    (h0 : ∃ v, placeVal (machine (kernel 1)) s pb = some v ∧ ValRep lbl w0.val v)
    (h1 : ∃ v, placeVal (machine (kernel 1)) s p2 = some v ∧ ValRep lbl w1.val v)
    (h2 : ∃ v, placeVal (machine (kernel 1)) s p3 = some v ∧ ValRep lbl w2.val v)
    (hc : ∃ v, placeVal (machine (kernel 1)) s pc = some v ∧ lbl l = some v)
    (hm : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s (boxPubCtlH c0 ty l) [] := by
  have hcc : TermRun.lookupE (boxPubCtlH c0 ty l).env "c" =
      some (.ptr .pub ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) := by
    simp [boxPubCtlH, TermRun.lookupE]
  have hmm : TermRun.lookupE (boxPubCtlH c0 ty l).env "me" =
      some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [boxPubCtlH, TermRun.evalAt, TermRun.lookupE] using hme
  have hss : TermRun.lookupE (boxPubCtlH c0 ty l).env "sl" = some (Spike.Lib.X64HelloSplit.slTy, [w0, w1, w2]) := by
    simpa [boxPubCtlH, TermRun.evalAt, TermRun.lookupE] using hsl
  refine placedSE_of_tbl [("c", [.one pc]), ("me", [.one pm]), ("sl", [.one pb, .one p2, .one p3])] ?_ ?_ ?_
  · intro x hx ty' ws hl
    have hfv : ∀ y ∈ exprFv (boxPubCtlH c0 ty l).term, y = "sl" ∨ y = "c" ∨ y = "me" := by
      show ∀ y ∈ exprFv Spike.Lib.X64HelloMainPreSrc.p0Term, _
      decide
    rcases hfv x hx with rfl | rfl | rfl
    · rw [hss] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hcc] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hmm] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty' ws hpl hl k wp wd hwp hwd
    by_cases ec : x = "c"
    · subst ec; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hcc] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at hc
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hmm] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at hm
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl
      rw [hss] at hl; cases hl
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact h0
      | 1, hwp, hwd => cases hwp; cases hwd; exact h1
      | 2, hwp, hwd => cases hwp; cases hwd; exact h2
    · simp [List.lookup, beq_false_of_ne ec, beq_false_of_ne em, beq_false_of_ne es] at hpl
  · intro x pls k n hpl hn'
    by_cases ec : x = "c"
    · subst ec; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl
      match k, hn' with
      | 0, hn' => cases hn'
      | 1, hn' => cases hn'
      | 2, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne ec, beq_false_of_ne em, beq_false_of_ne es] at hpl

variable {R : Region}

/-- **main's source past the publication placed at `wc_main`'s slots**: the source before it at the box's fence
(`QBH`, for its `me` and `sl`), the slice (`SlRep` at `w0`, `w2`, `w3`) at `-8`, `-24`, `-32`, the box's cell `b`
at `-48` and main's id `t0` at `-40`. -/
theorem placedSE_pubSlotsH {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c0 : Ctl} {ty : Ty}
    {l l' : WeakMem.AllocLabel} {A : Nat} {ws : List TermRun.Word} {w0 w1 w2 w3 b t0 : Nat}
    (hsrc : QBH l b ws l' A c0) (hsl : SlRep lbl ws w0 w1 w2 w3) (hb : lbl l = some b)
    (ht : lbl (mainTidLbl 2) = some t0) (hP : SlotPH R b t0 s.st.1) (hS : SlotSlH R w0 w2 w3 s.st.1) :
    PlacedSE Λ lbl s (boxPubCtlH c0 ty l) [] := by
  obtain ⟨-, -, -, -, -, hme, hsl'⟩ := hsrc
  obtain ⟨lr, rfl, hl, -, rfl, rfl⟩ := hsl
  obtain ⟨p48, p40⟩ := Ti2.slotPH_place hP
  obtain ⟨s0, s2, s3⟩ := hS
  exact placedSE_pubAtH _ _ _ _ _ hme hsl'
    ⟨_, slotRdH_place s0, by decide, w0, by simp [Scc.Sem.wordAddr, hl], by simp⟩
    ⟨_, slotRdH_place s2, by decide, rfl⟩ ⟨_, slotRdH_place s3, by decide, rfl⟩ ⟨_, p48, hb⟩ ⟨_, p40, ht⟩

/-- **`SpawnPl.hplQ_GJ1H` past the publication**: at a ghost of `GJ1H`, the published control
`boxPubCtlH c0 ty l` of a source `c0` at the box's fence is placed at the twice extended placement wherever the
slots read `b'`, `me` and `sl`. -/
theorem hplP_GJ1H {L : RuntimeLayout} {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat}
    {F : MachineData → Prop} {J1 : Spike.Lib.X64.AS → Ctl → Prop} {t : UInt64}
    (hl' : lbl1 l' = none) (hmt : lbl1 (mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.X64HelloH2G.GJ1H L lbl1 lr R F J1 t) :
    ∀ c0 ty l sl me cA fr, MidPGH (QBH l' b' (slWsH lr)) c0 ty l cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b' me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE L.Λ (Spike.Lib.X64ConsumerA.upd lbl1 l' b') s (boxPubCtlH c0 ty l) [] := by
  rintro c0 ty l sl me cA fr ⟨⟨hsrc, -⟩, σe, c, hJ, -, rfl, rfl⟩ s ⟨hP, hS⟩
  obtain ⟨rfl, -⟩ := id hsrc
  obtain ⟨hsl, hme⟩ := Spike.Lib.X64HelloH2G.hG_of (b' := b') hl' hmt R F J1 t hG σe c hJ
  exact placedSE_pubSlotsH hsrc hsl (by simp [Spike.Lib.X64ConsumerA.upd]) hme hP hS

/-! ## Nodes and blocks placed at the slots -/

variable {exe : _root_.Executable} {endPc : Int64} {F F₂ : MachineData → Prop} {Λ : Scc.Sem.Layout}
  {lbl : Lbl}

/-- **A node's states placed at the slots**: every state of `n.J σ c` is placed (`lbl`) wherever the five slots
read `σ`'s words. -/
def PlH (Λ : Scc.Sem.Layout) (lbl : Lbl) (R : Region) (n : ND) : Prop :=
  ∀ σ c, n.J σ c → ∀ s : State, SlotPH R (σ.slot (-48)).toNat (σ.slot (-40)).toNat s.st.1 ∧
    SlotSlH R (σ.slot (-8)).toNat (σ.slot (-24)).toNat (σ.slot (-32)).toNat s.st.1 → PlacedSE Λ lbl s c []

/-- **A node placed at the slots is inside `PlacedSE`**, at no move. -/
theorem nodeW_plH (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {n : ND} (h : PlH Λ lbl R n) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨_, _, _, _, σ, hA, _, hj⟩ => ⟨h σ c hj s (slots_absH hlo hhi hA), fun _ h => h⟩

/-- **The block keeps the five slots** from the offsets `o`. -/
def KeepsH (o : Spike.Lib.X64.SO) (blk : List (Directive × Nat)) : Bool :=
  ([-48, -40, -8, -24, -32] : List Int).all fun j => keepsSlot j o blk

/-- **A block keeping the five slots, its node placed at them, is inside `PlacedSE`**, at no move
(`WakeSrcCtl.arun_slot_keep`). -/
theorem blkW_plH (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {n : ND} {blk : List (Directive × Nat)} (h : PlH Λ lbl R n)
    (hk : KeepsH n.o blk = true) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  have e : ∀ j ∈ ([-48, -40, -8, -24, -32] : List Int),
      (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot j =
        σ.slot j :=
    fun j hm => arun_slot_keep _ j blk ⟨n.pc, n.o, σ⟩ k (List.all_eq_true.mp hk j hm)
  have hs := slots_absH hlo hhi hA
  rw [e (-48) (by simp), e (-40) (by simp), e (-8) (by simp), e (-24) (by simp), e (-32) (by simp)] at hs
  exact ⟨h σ c hj _ hs, fun _ h => h⟩

/-! ## `wc_main`'s blocks keep the five slots -/

theorem keepsH_res : KeepsH ⟨-128, [(.rbp, 0)]⟩ resBH = true := by decide +kernel
theorem keepsH_tcb2 : KeepsH oWH tcb2CallH = true := by decide +kernel
theorem keepsH_sp4 : KeepsH oWH sp4AH = true := by decide +kernel
theorem keepsH_init : KeepsH oWH initCallH = true := by decide +kernel
theorem keepsH_sp6 : KeepsH oWH sp6AH = true := by decide +kernel
theorem keepsH_clone : KeepsH oWH cloneLdH = true := by decide +kernel
theorem keepsH_nr : KeepsH oWH Spike.Lib.X64.WakePh.WcClone.nrB = true := by decide +kernel

/-! ## `wc_main`'s own nodes placed -/

section Main

variable {ms : Spike.Lib.MemSide isa} {J1 : Spike.Lib.X64.AS → Ctl → Prop} {l : WeakMem.AllocLabel}
  {b : Nat} {ws : List TermRun.Word}

/-- **A node before the publication placed at the slots**: its states at the ghost's source `c0` and frame's
words (`FrWH`), placed wherever the slots read `b`, `me` and `sl` (`HsQ`). -/
theorem plH_mid
    (HsQ : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hM : MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me) {n : ND}
    (hJ : ∀ σ c, n.J σ c → c = c0 ∧ FrWH sl me cA fr σ) : PlH Λ lbl R n := by
  intro σ c hj s hs
  obtain ⟨rfl, h8, -, h24, h32, h40, h48, -, -⟩ := hJ σ c hj
  obtain ⟨_, _, ⟨-, hAb, -⟩, hcA⟩ := hM.1
  rw [h48, h40, h8, h24, h32, hcA, hAb] at hs
  exact HsQ c sl me cA fr hM s hs

/-- **A node past the publication placed at the slots**: its states at the published control
`boxPubCtlH c0 ty l'` and the frame's words (`FrWH`), placed wherever the slots read `b`, `me` and `sl` (`HsP`). -/
theorem plH_pub
    (HsP : ∀ c0 ty l' sl me cA fr, MidPGH (QBH l b ws) c0 ty l' cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s (boxPubCtlH c0 ty l') [])
    {c0 : Ctl} {ty : Ty} {l' : WeakMem.AllocLabel} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hM : MidPGH (QBH l b ws) c0 ty l' cA ∧ FrMGH J1 fr sl me) {n : ND}
    (hJ : ∀ σ c, n.J σ c → c = boxPubCtlH c0 ty l' ∧ FrWH sl me cA fr σ) : PlH Λ lbl R n := by
  intro σ c hj s hs
  obtain ⟨rfl, h8, -, h24, h32, h40, h48, -, -⟩ := hJ σ c hj
  obtain ⟨-, hAb, -⟩ := hM.1.1
  rw [h48, h40, h8, h24, h32, hAb] at hs
  exact HsP c0 ty l' sl me cA fr hM s hs

/-- **`WcMainWH` at `PlacedSE`** (`WcW2.wcWf_W2H`'s `hpl`): `wc_main`'s own nodes placed at `lbl`, from main's
source at the box's fence (`HsQ`, at `QBH`) and past the publication (`HsP`, at `boxPubCtlH`) placed wherever the
slots read the cell `b`, main's word `me` and the slice `sl` (`SpawnPl.hplQ_GJ1H`, `hplP_GJ1H`). -/
theorem wcMainW_plH (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (HsQ : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (HsP : ∀ c0 ty l' sl me cA fr, MidPGH (QBH l b ws) c0 ty l' cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s (boxPubCtlH c0 ty l') []) :
    WcMainWH (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F F₂ ms J1 (QBH l b ws) := by
  refine ⟨blkW_plH hlo hhi ?_ keepsH_res, fun c0 sl me cA fr hM => ?_,
    fun c0 sl me cA fr hM => ⟨?_, ?_, ?_⟩, fun c0 ty l' sl me cA fr hM => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- the reserve's call block
  · rintro σ c ⟨⟨l', A, ⟨q, ⟨σe, hJ1, -, -, h8, -, h24, h32, h40⟩, hA, -⟩, hQ⟩, -⟩ s hs
    rw [hA, hQ.2.1, h40, h8, h24, h32] at hs
    exact HsQ c _ _ (σ.slot (-48)) (σe.regs.rbp.toBitVec, σe.slot 0)
      ⟨⟨l', A, hQ, hA⟩, σe, q.1.c0, hJ1, rfl, rfl, rfl⟩ s hs
  -- `.x23`
  · exact blkW_plH hlo hhi (plH_mid HsQ hM fun _ _ h => ⟨h.1, h.2.2⟩) keepsH_tcb2
  -- `.x24`'s block, the tid store, `scc_rt_thread_init`'s call block
  · exact blkW_plH hlo hhi (plH_mid HsQ hM fun _ _ h => ⟨h.1, h.2.2.1⟩) keepsH_sp4
  · exact nodeW_plH hlo hhi (plH_mid HsQ hM fun _ _ h => ⟨h.1, h.2.2.2.2.1⟩)
  · exact blkW_plH hlo hhi (plH_mid HsQ hM fun _ _ h => ⟨h.1, h.2.2⟩) keepsH_init
  -- `.x25`: before the `mfence` at `c0`, past it at the published control
  · have hM' : MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me := ⟨⟨l', cA.toNat, hM.1.1, rfl⟩, hM.2⟩
    exact blkW_plH hlo hhi (plH_mid HsQ hM' fun _ _ h => ⟨h.1, h.2.2.2⟩) keepsH_sp6
  · have hM' : MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me := ⟨⟨l', cA.toNat, hM.1.1, rfl⟩, hM.2⟩
    exact nodeW_plH hlo hhi (plH_mid HsQ hM' fun _ _ h => ⟨h.1, h.2.2.2.2⟩)
  · exact blkW_plH hlo hhi (plH_pub HsP hM fun _ _ h => ⟨h.1, h.2.2.2.2⟩) keepsH_clone
  · exact nodeW_plH hlo hhi (plH_pub HsP hM fun _ _ h => ⟨h.1.1, h.1.2.2.2.2⟩)
  · exact nodeW_plH hlo hhi (plH_pub HsP hM fun _ _ h => ⟨h.1.1.1, h.1.1.2.2.2.2⟩)
  · exact blkW_plH hlo hhi (plH_pub HsP hM fun _ _ h => ⟨h.1.1.1, h.1.1.2.2.2.2⟩) keepsH_nr

end Main

/-- **`WcW2.wcWf_W2H`'s `hpl` at a ghost of `GJ1H`** (rodata's label `lr`, the box's `l'` fresh at `lbl1`, main's
id at the TCB): `wc_main`'s own nodes placed at the twice extended placement `upd lbl1 l' b'` (`wcMainW_plH` at
`SpawnPl.hplQ_GJ1H`, `hplP_GJ1H`). -/
theorem wcMainW_plGJ1H {L : RuntimeLayout} {ms : Spike.Lib.MemSide isa}
    {J1 : Spike.Lib.X64.AS → Ctl → Prop} {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat}
    {F' : MachineData → Prop} {t : UInt64} (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hl' : lbl1 l' = none) (hmt : lbl1 (mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.X64HelloH2G.GJ1H L lbl1 lr R F' J1 t) :
    WcMainWH (fun s c => PlacedSE L.Λ (Spike.Lib.X64ConsumerA.upd lbl1 l' b') s c []) (fun _ _ => False) exe endPc
      R F F₂ ms J1 (QBH l' b' (slWsH lr)) :=
  wcMainW_plH hlo hhi (SpawnPl.hplQ_GJ1H hl' hmt hG) (hplP_GJ1H hl' hmt hG)

end Spike.Lib.X64.HelloPh.WcPl2

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WcPl2.placedSE_pubAtH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPl2.placedSE_pubAtH

/-- info: 'Spike.Lib.X64.HelloPh.WcPl2.hplP_GJ1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPl2.hplP_GJ1H

/-- info: 'Spike.Lib.X64.HelloPh.WcPl2.blkW_plH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPl2.blkW_plH

/-- info: 'Spike.Lib.X64.HelloPh.WcPl2.wcMainW_plH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPl2.wcMainW_plH

/-- info: 'Spike.Lib.X64.HelloPh.WcPl2.wcMainW_plGJ1H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPl2.wcMainW_plGJ1H
