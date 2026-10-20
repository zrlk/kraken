/-
**The x64 Michael–Scott queue protocol for try-once dequeuers that do not
read `tail`.** ISA-neutral.

`EnvG/X64MsQueue2Ghost.lean`'s `form` fits msqueue2's dequeuer only: its
`HeadF` needs the swing's `tail` read `t ≠ head` (with its windows). A
dequeuer that reads `head`, then the link `[head]`, returns empty on a `0`
link and otherwise swings `head` to the link once (retrying only when the
`head` CAS fails) reads no `tail`, and can swing `head` past `tail` (the
enqueuer has linked a node but not yet swung `tail`). This file is the
variant protocol for such dequeuers, on the same layout (`Params`,
`QLocs`), plans of the enqueuer (`planE`) and link and `tail` facts
(`LinkF`, `TailF`, `TailLoc`):

- `HeadFW` (the dequeuer's swing of `head` at `V`): AArch64's
  `MsQueue2Ghost.HeadF` with the link at offset `0`: the overwritten message
  `z` is adjacent, and the value written is the non-zero value of a message
  of `[z]` below `V`. No `tail` read and no window on the link read.
- `formW`: `form` with `HeadFW` for `HeadF`, and one more clause at `head`
  for untracked parameters (`P.trk = false`): a write of `n1` holds the
  dequeuer's token `P.tokQ` whole, or an earlier `head` message of `n1` lies
  below it. The final law reads off it that a `head` message of `n1` was
  written by the holder of `tokQ` (`X64MsQueueWFinal.lean`).
- `planDW`: the dequeuer's plan: as `planD`, and a write of `n1` to `head`
  gives `tokQ`.
- The initial resources `tResW` (`tokQ` moves from the enqueuer to the
  dequeuer) and the initial erasure `erase_initW`, from the generic
  `erase_init_ghostQ` (any impure predicate at the queue words; `ghost₀` is
  its instance at `form`).
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2Final
import Kraken.Promising.SLR.InitGhost

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq read?_mono)

variable {I : ISA}

/-! ## The swing and the predicate -/

/-- **The try-once dequeuer's swing of `head`** at `V`: it overwrote the
adjacent message `z` and writes `v ≠ 0`, the value of a message of `[z]`
below `V`. -/
def HeadFW (P : Params) (m : Memory) (V : View) (v : Val) : Prop :=
  BitVec.setWidth 64 v ≠ 0 ∧ ∃ tr z b y, tr < V ∧ m.read? P.head tr = some z ∧ NoMsgIn m P.head tr V ∧
    b < V ∧ m.read? ⟨BitVec.setWidth 64 z, 8⟩ b = some y ∧ BitVec.setWidth 64 y = BitVec.setWidth 64 v

theorem HeadFW.mono {P : Params} {m m' : Memory} (h : m.Prefix m') {V : View} {v : Val} (hV : V ≤ m.last + 1)
    (hh : HeadFW P m V v) : HeadFW P m' V v :=
  let ⟨hnz, tr, z, b, y, h1, h2, h3, h4, h5, h6⟩ := hh
  ⟨hnz, tr, z, b, y, h1, read?_mono h h2, h3.mono h hV, h4, read?_mono h h5, h6⟩

/-- **The dequeuer's token** (a ghost location of `6` bytes: no access of
the code has that width): whoever writes `n1` to `head` holds it. -/
def Params.tokQ (P : Params) : Loc := ⟨P.h, 6⟩

/-- The `n1` clause at `head`: untracked parameters, a write of `n1` holds
`tokQ` whole or lies above an earlier `head` message of `n1`. -/
def TokN1 (P : Params) (m : Memory) (V : View) (R : Res) (v : Val) : Prop :=
  P.trk = false → BitVec.setWidth 64 v = P.n1 → TokFrozen P.tokQ R ∨ ∃ V' < V, Deq m P V' P.n1

/-- **The predicate of the queue words for try-once dequeuers.** -/
def formW (P : Params) : Pred where
  P v m V R := V ≠ 0 → ∃ x w, m.get? V = some ⟨x, v, w⟩ ∧ (P.IsL x → LinkF P m V R x v) ∧
    (x = P.head → HeadFW P m V v ∨ TailLoc P m V x) ∧
    (x = P.tail → TailF P m V v ∨ TailLoc P m V x) ∧
    (x = P.head → TailLoc P m V x ∨ P.HW w R) ∧
    (x = P.head → TailLoc P m V x ∨ TokN1 P m V R v)
  mono v m m' V R hpre h := by
    intro hV
    obtain ⟨x, w, hg, h1, h2, h3, h4, h5⟩ := h hV
    have hle : V ≤ m.last + 1 := Nat.le_succ_of_le (m.last_le_of_get?_eq_some hg)
    refine ⟨x, w, Memory.get?_of_prefix hpre.2 hg, fun hx => ?_, fun hx => ?_, fun hx => ?_,
      fun hx => (h4 hx).imp (TailLoc.mono hpre) id, fun hx => ?_⟩
    · obtain ⟨h4, h5, h6⟩ := h1 hx
      exact ⟨h4.imp id fun h7 => ⟨h7.1, h7.2.1, h7.2.2.mono hpre⟩, h5.mono hpre, h6.mono hpre hle⟩
    · exact (h2 hx).imp (HeadFW.mono hpre hle) (TailLoc.mono hpre)
    · exact (h3 hx).imp (TailF.mono hpre hle) (TailLoc.mono hpre)
    · exact (h5 hx).imp (TailLoc.mono hpre) fun h6 ht hn =>
        (h6 ht hn).imp id fun ⟨V', hV', hd⟩ => ⟨V', hV', hd.mono hpre⟩

theorem formW_not_pure (P : Params) (v : Val) : ¬ Pred.Pure (formW P) v := by
  intro h
  obtain ⟨x, w, hg, -⟩ := h { init := [], msgs := #[] } 1 (by decide)
  simp [Memory.get?] at hg

/-! ## The initial ghost, for any predicate at the queue words -/

/-- **The queue's initial ghost for a predicate `F`** at the queue words
(`Pred.emp` elsewhere): acquire table `[F]`, the initial messages of the
queue words in release mode with unit slots for id `0`. -/
abbrev ghostQ (P : Params) (F : Pred) : Ghost :=
  initGhostAcq (fun x => if P.IsW x then F else Pred.emp) [F] (wList P) ((wList P).map fun x => (x, 0, Res.unit))

theorem ghostQ_form (P : Params) : ghostQ P (form P) = ghost₀ P := by
  simp [ghostQ, initGhostAcq, ghost₀, List.map_map, Function.comp_def]

/-- The initial ghost of the try-once protocol. -/
def ghost₀W (P : Params) : Ghost := ghostQ P (formW P)

theorem ghostQ_rel_w {P : Params} {F : Pred} {x : Loc} (h : P.IsW x) : (ghostQ P F).rel x = F := by
  simp [ghostQ, initGhostAcq, h]

theorem ghostQ_rel_ne {P : Params} {F : Pred} {x : Loc} (h : ¬ P.IsW x) : (ghostQ P F).rel x = Pred.emp := by
  simp [ghostQ, initGhostAcq, h]

/-- **The ghost facts of the try-once protocol**: the release predicates of
`ghost₀W`, an acquire table extending `[formW]`. -/
def GWW (P : Params) (g : Ghost) : Prop :=
  g.rel = (ghost₀W P).rel ∧ (ghost₀W P).acqTab <+: g.acqTab

namespace GWW

variable {P : Params} {g g' : Ghost}

theorem mono (h : GWW P g) (hle : g.Le g') : GWW P g' := ⟨hle.rel.trans h.1, h.2.trans hle.acqTab⟩

theorem rel_w (h : GWW P g) {x : Loc} (hx : P.IsW x) : g.rel x = formW P := by rw [h.1]; exact ghostQ_rel_w hx

theorem rel_ne (h : GWW P g) {x : Loc} (hx : ¬ P.IsW x) : g.rel x = Pred.emp := by
  rw [h.1]; exact ghostQ_rel_ne hx

theorem acqPred_zero (h : GWW P g) : g.acqPred 0 = formW P :=
  Ghost.acqPred_of_prefix h.2 (by simp [ghost₀W, ghostQ, initGhostAcq])

theorem impure (h : GWW P g) {x : Loc} (hx : P.IsW x) (v : Val) : ¬ Pred.Pure (g.rel x) v := by
  rw [h.rel_w hx]; exact formW_not_pure P v

end GWW

theorem ghost₀W_gww (P : Params) : GWW P (ghost₀W P) := ⟨rfl, List.prefix_refl _⟩

/-! ## The dequeuer's plan -/

/-- **The dequeuer's plan**: every write to a queue word is a release; a
write of `n1` to `head` gives `tokQ`, any other nothing. -/
def planDW (P : Params) : Plan :=
  ⟨{ loc := P.head, val := some (BitVec.setWidth 128 P.n1), gives := [P.tokQ] } :: (planD P).entries⟩

theorem planDW_find (P : Params) (l : Loc) (v : Val) : (planDW P).find? l v =
    if l = P.head ∧ v = BitVec.setWidth 128 P.n1 then
      some { loc := P.head, val := some (BitVec.setWidth 128 P.n1), gives := [P.tokQ] }
    else (planD P).find? l v := by
  unfold Plan.find?
  simp only [planDW, List.find?_cons]
  by_cases h : l = P.head ∧ v = BitVec.setWidth 128 P.n1
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right h]
    have : (decide (P.head = l) && decide (BitVec.setWidth 128 P.n1 = v)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; grind
    rw [this]

theorem planDW_valid (P : Params) : (planDW P).Valid := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · simp [Params.tokQ, Params.head]
  · exact planD_valid P e he

theorem planDW_whole (P : Params) (l : Loc) (v : Val) : (planDW P).Whole l v :=
  Plan.Whole.of_entries (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · simp only [planD, List.mem_map] at he; obtain ⟨x, -, rfl⟩ := he; rfl) l v

theorem planDW_rel (P : Params) (l : Loc) (v : Val) : (planDW P).rel l v = decide (P.IsW l) := by
  unfold Plan.rel; rw [planDW_find]
  split
  · next h => simp [h.1, Params.IsW]
  · exact planD_rel P l v

theorem planDW_gives (P : Params) (l : Loc) (v : Val) :
    (planDW P).gives l v = if l = P.head ∧ v = BitVec.setWidth 128 P.n1 then [P.tokQ] else [] := by
  unfold Plan.gives; rw [planDW_find]
  split
  · rfl
  · exact planD_gives P l v

theorem not_mem_planDW_gives {P : Params} {x : Loc} (hx : x ≠ P.tokQ) (l : Loc) (v : Val) :
    x ∉ (planDW P).gives l v := by
  rw [planDW_gives]; split <;> simp [hx]

/-- **A whole release keeps the fraction of every location it does not
give** (any plan). -/
theorem Plan.after_q_of_not_mem (pl : Plan) {l : Loc} {v : Val} (hs : pl.Whole l v) (tw : Time) (cl : Prop)
    (r : Res) {x : Loc} (hx : x ∉ pl.gives l v) : ((pl.after l v tw cl r).wr x).q = (r.wr x).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, pl.keep_of_whole hs]
    show (if x ∈ pl.gives l v then Perm.unit else r.wr x).q = _
    rw [ite_eq_right hx]
  · rw [Res.addW_q]

/-- **A whole release keeps the acquire ids of every location it does not
give** (any plan). -/
theorem Plan.after_acq_of_not_mem (pl : Plan) {l : Loc} {v : Val} (hs : pl.Whole l v) (tw : Time) (cl : Prop)
    (r : Res) {x : Loc} (hx : x ∉ pl.gives l v) (ι : PredId) : (pl.after l v tw cl r).acq x ι = r.acq x ι := by
  unfold Plan.after
  split
  · rw [Res.addW_acq, pl.keep_of_whole hs]
    show (if x ∈ pl.gives l v then 0 else r.acq x ι) = _
    rw [ite_eq_right hx]
  · rw [Res.addW_acq]

/-! ## The initial resources -/

/-- The enqueuer's initial fractions: `fracE` without `tokQ`. -/
def fracEW (P : Params) (x : Loc) : Rat := if x = P.tokQ then 0 else fracE P x

/-- The dequeuer's initial fractions: `fracD` and `tokQ` whole. -/
def fracDW (P : Params) (x : Loc) : Rat := if x = P.tokQ then 1 else fracD P x

theorem fracEW_nonneg (P : Params) (x : Loc) : 0 ≤ fracEW P x := by
  unfold fracEW; split; · grind
  · exact fracE_nonneg P x

theorem fracDW_nonneg (P : Params) (x : Loc) : 0 ≤ fracDW P x := by
  unfold fracDW; split; · grind
  · exact fracD_nonneg P x

theorem fracW_add_le (P : Params) (x : Loc) : fracEW P x + fracDW P x ≤ 1 := by
  unfold fracEW fracDW; split; · grind
  · exact frac_add_le P x

/-- The enqueuer's initial resource (no acquire id). -/
def resEW (m : Memory) (P : Params) : Res := Res.initOf m (fracEW P) (fracEW_nonneg P)

/-- The dequeuer's initial resource: half of `head`/`tail`, `tokQ` and the
acquire id `0` of every queue word. -/
def resDW (m : Memory) (P : Params) : Res :=
  ⟨(Res.initOf m (fracDW P) (fracDW_nonneg P)).wr, fun x ι => if P.IsW x ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: the enqueuer is thread `0`, the dequeuer
thread `1`. -/
def tResW (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then resEW m P else if i = 1 then resDW m P else Res.unit

/-! ## Initial erasure -/

section Init

/-- **Initial erasure of the queue for any predicate `F`** at the queue words
that holds at view `0`, for any thread resources whose total holds the
acquire id `0` of every queue word once, at most a whole write fraction of
every location, and only the initial message in its write sets. -/
theorem erase_init_ghostQ {P : Params} (hL : QLocs P) {F : Pred} (hF0 : ∀ v m r, F.P v m 0 r) (T : Nat → Prop)
    {states : List I.State} {initMem : List (Loc × Val)} {rF : Nat → Res}
    (ha : ∀ x ι, (total rF (ghostQ P F) (Config.init states initMem)).acq x ι = if P.IsW x ∧ ι = 0 then 1 else 0)
    (hq : ∀ x, ((total rF (ghostQ P F) (Config.init states initMem)).wr x).q ≤ 1)
    (hX : ∀ x, 0 < ((total rF (ghostQ P F) (Config.init states initMem)).wr x).q → ∀ p,
      ((total rF (ghostQ P F) (Config.init states initMem)).wr x).X p ↔
        p = ((Config.init states initMem).mem.initVal x, 0)) :
    Erase rF (ghostQ P F) T (Config.init states initMem) := by
  refine erase_initGhostAcq T ?_ ⟨hq, fun x ι => by rw [ha]; split <;> omega⟩ (fun x ι h => ?_)
    (fun x v m V r h => ?_) hX (fun x hx => ?_) (fun e he => ?_) (fun x hx ι => ?_) (fun e he => ?_) (fun e he => ?_)
  · have h1 := hL.head_tail; have h2 := hL.head_ls; have h3 := hL.head_l1; have h4 := hL.tail_ls
    have h5 := hL.tail_l1; have h6 := hL.ls_l1; have h7 := hL.head_l2; have h8 := hL.tail_l2
    have h9 := hL.ls_l2; have h10 := hL.l1_l2
    simp [wList, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · rw [ha] at h; show ι < 1; split at h <;> grind
  · have hids : (ghostQ P F).acqIds (total rF (ghostQ P F) (Config.init states initMem)).acq x =
        if P.IsW x then [0] else [] := by
      simp only [Ghost.acqIds]
      rw [show (ghostQ P F).acqTab.length = 1 from rfl]
      by_cases hx : P.IsW x <;> simp [hx, ha]
    rw [Ghost.acqPreds, hids]
    by_cases hx : P.IsW x
    · simp only [hx, ↓reduceIte] at h ⊢
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, rfl⟩
    · simp only [hx, ↓reduceIte] at h ⊢; exact h
  · simp only [show ¬ P.IsW x from fun h => hx (mem_wList.mpr h), ↓reduceIte]; exact Pred.emp_pure _
  · simp only [List.mem_map] at he; obtain ⟨x, -, rfl⟩ := he; simp
  · rw [ha]; simp only [mem_wList.mp hx, true_and, List.mem_map]
    exact ⟨fun h => by split at h <;> grind, fun ⟨_, ⟨y, _, he⟩, _, h⟩ => by cases he; simp [← h]⟩
  · simp only [List.mem_map] at he; obtain ⟨x, hx, rfl⟩ := he; exact hx
  · simp only [List.mem_map] at he; obtain ⟨x, -, rfl⟩ := he; exact hF0 _ _ _

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

/-- **Initial erasure of the try-once queue** (enqueuer thread `0`, dequeuer
thread `1`). -/
theorem erase_initW {P : Params} (hL : QLocs P) (T : Nat → Prop) :
    Erase (tResW (Config.init [s0, s1] initMem).mem P) (ghost₀W P) T (Config.init [s0, s1] initMem) := by
  have htot : total (tResW (Config.init [s0, s1] initMem).mem P) (ghostQ P (formW P)) (Config.init [s0, s1] initMem) =
      (resEW (Config.init [s0, s1] initMem).mem P).op (resDW (Config.init [s0, s1] initMem).mem P) := by
    simp only [total, Config.init_size, threadsRes, List.length_cons, List.length_nil]
    rw [show (ghostQ P (formW P)).slotsRes = Res.unit by simp [Ghost.slotsRes, ghostQ, initGhostAcq, wList,
      Res.prod, Res.op_unit], Res.op_unit]
    show Res.prod [tResW _ P 0, tResW _ P 1] = _
    simp [tResW, Res.op_unit]
  refine erase_init_ghostQ hL (fun _ _ _ h => absurd rfl h) T (fun x ι => ?_) (fun x => ?_) ?_
  · rw [htot]; show 0 + (if P.IsW x ∧ ι = 0 then 1 else 0) = _; simp
  · rw [htot]; exact fracW_add_le P x
  intro x hpos p
  rw [htot] at hpos ⊢
  change 0 < fracEW P x + fracDW P x at hpos
  show (0 < fracEW P x ∧ p = _) ∨ (0 < fracDW P x ∧ p = _) ↔ _
  have := fracEW_nonneg P x; have := fracDW_nonneg P x
  by_cases h0 : 0 < fracEW P x
  · simp [h0]
  · have h1 : 0 < fracDW P x := by grind
    simp [h0, h1]

end Init

end Kraken.Promising.X64.EnvG.MsQueueX
