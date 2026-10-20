/-
Conservativity for AArch64: Kraken's single-threaded judgment carries over to
promise-free runs of the Promising machine (`Kraken.Promising.SeqLink`).

A thread of the Promising machine runs `Executable.step` on its private
`dmem`; the shared locations are not in it, so their accesses reach the
memory model. Kraken's judgment (`Effects.All`) is about a *merged* memory
that has the shared locations mapped, holding their last writes
(`Kraken.Promising.MergedMem`). The link is a simulation of the split run by
the merged one, instruction by instruction:

- `Effects.AllMem tid mem Q`: the split tree, its unmapped accesses served
  sequentially by the Promising memory `mem`. Sound for the translated event
  tree (`allMem_sound`).
- `Effects.AllW L P`: `Effects.All P` that also asks every access to respect
  the layout `L` of shared locations (`SharedLayout.Ok`: exactly a location's
  address and width, or off the footprint). `allW_iff`: it is `All` together
  with that access discipline; `allW_nil`: without shared locations it is
  `All`.
- `step_sim`: one `Executable.step` from related states, merged under `AllW`,
  split under `AllMem`. It is proved per primitive (`load_sim`, `storeK_sim`,
  `rmwK_sim`, `loadPairK_sim`, ...) and by one search over the instruction set
  (`operation_sim`).
- `merged_link`: an `Eventually (step1W L e) P` judgment about the merged
  state carries over to every promise-free run of the one-thread machine.
  `merged_link_halt`: a run that reaches the end address ends in a state whose
  merge satisfies `P`. With `L = []` the merge is the private memory itself
  (`MemRel.nil`, `step1W_nil`).

Kraken's kstep proofs conclude `Eventually (straightlineStep e)`, a judgment
over segment bursts; carrying those over to `step1W` is not done here.
-/
import Kraken.Promising.AArch64
import Kraken.Promising.SeqLink
import Kraken.Promising.MergedMem
import Kraken.AArch64.OmniSemantics

open Std

namespace Kraken.Promising.AArch64

/-! ## The split run: unmapped accesses against the Promising memory -/

/-- Every run of the tree, with the accesses outside `dmem` served
sequentially by the Promising memory `mem` (as `seqRun` serves them), ends in
a state and memory satisfying `Q`. Total, like `Effects.All`. -/
def _root_.Effects.AllMem (tid : Nat) (mem : Memory) (Q : MachineState → Memory → Prop) : Effects → Prop
  | .done a => Q a mem
  | .unimplemented _ => False
  | .unaligned_sp _ => False
  | .nonmem_load dmem addr w ret => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid mem Q
  | @Effects.nonmem_store dmem addr w v ret =>
    (ret dmem).AllMem tid (mem.append { loc := loc addr w.bytes, val := v.setWidth 128, tid }).1 Q
  | .sync_load _ _ dmem addr w ret => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid mem Q
  | @Effects.sync_store _ xcl dmem addr w v ret =>
    (ret true dmem).AllMem tid (mem.append { loc := loc addr w.bytes, val := v.setWidth 128, tid }).1 Q ∧
      (xcl = true → (ret false dmem).AllMem tid mem Q)
  | .rmw _ _ dmem addr w op ret =>
    match op ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) with
    | some v => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid
        (mem.append { loc := loc addr w.bytes, val := v.setWidth 128, tid }).1 Q
    | none => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid mem Q
  | .sync_load_pair _ _ dmem addr w ret =>
    (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits)
      ((mem.finalVal (loc (addr + w.bytesv) w.bytes)).setWidth w.bits) dmem).AllMem tid mem Q
  | @Effects.sync_store_pair _ xcl dmem addr w v1 v2 ret =>
    (ret true dmem).AllMem tid ((mem.append { loc := loc addr w.bytes, val := v1.setWidth 128, tid }).1.append
      { loc := loc (addr + w.bytesv) w.bytes, val := v2.setWidth 128, tid }).1 Q ∧
      (xcl = true → (ret false dmem).AllMem tid mem Q)
  | @Effects.rmw_pair _ dmem addr w cmp1 cmp2 new1 new2 ret =>
    -- `toEv` (`caspTree`) performs the halves in either order: on success, both
    -- orders of the two appends
    let o1 := (mem.finalVal (loc addr w.bytes)).setWidth w.bits
    let o2 := (mem.finalVal (loc (addr + w.bytesv) w.bytes)).setWidth w.bits
    let w1 : Msg := { loc := loc addr w.bytes, val := new1.setWidth 128, tid }
    let w2 : Msg := { loc := loc (addr + w.bytesv) w.bytes, val := new2.setWidth 128, tid }
    if o1 == cmp1 && o2 == cmp2 then
      (ret o1 o2 dmem).AllMem tid ((mem.append w1).1.append w2).1 Q ∧
        (ret o1 o2 dmem).AllMem tid ((mem.append w2).1.append w1).1 Q
    else (ret o1 o2 dmem).AllMem tid mem Q
  | .fence _ ok => (ok ()).AllMem tid mem Q
  | @Effects.undefined α _ ret => ∀ v : α, (ret v).AllMem tid mem Q
  | .require_read_access _ _ ok => (ok ()).AllMem tid mem Q
  | .require_write_access _ _ ok => (ok ()).AllMem tid mem Q
  | .require_exec_access _ ok => (ok ()).AllMem tid mem Q

/-- The two halves of a pair access are distinct locations. -/
theorem loc_pair_ne (addr : BitVec 64) (w : MemWidth) : loc addr w.bytes ≠ loc (addr + w.bytesv) w.bytes := by
  intro h
  have h' := congrArg Loc.addr h
  simp only [loc] at h'
  cases w <;> simp [MemWidth.bytesv] at h' <;> bv_omega

/-- The sequential runs of `caspTree` (no declarations): the `AllMem` reading of
`rmw_pair`, for a continuation `ret` sound for `P`. -/
theorem caspTree_allSeq {σ : Type} {tid : Nat} {Q : σ → Memory → Prop} {k : RmwKind} {addr : BitVec 64}
    {w : MemWidth} {cmp1 cmp2 new1 new2 : w.type} {ret : w.type → w.type → EvTree σ}
    {P : w.type → w.type → Memory → Prop}
    (hret : ∀ o1 o2 mem, P o1 o2 mem → (ret o1 o2).AllSeq tid mem Q) {mem : Memory}
    (h : let o1 := (mem.finalVal (loc addr w.bytes)).setWidth w.bits
      let o2 := (mem.finalVal (loc (addr + w.bytesv) w.bytes)).setWidth w.bits
      let w1 : Msg := { loc := loc addr w.bytes, val := new1.setWidth 128, tid }
      let w2 : Msg := { loc := loc (addr + w.bytesv) w.bytes, val := new2.setWidth 128, tid }
      if o1 == cmp1 && o2 == cmp2 then
        P o1 o2 ((mem.append w1).1.append w2).1 ∧ P o1 o2 ((mem.append w2).1.append w1).1
      else P o1 o2 mem) :
    (caspTree {} k addr cmp1 cmp2 new1 new2 ret).AllSeq tid mem Q := by
  have hne := loc_pair_ne addr w
  have hne' := hne.symm
  simp only [loc] at hne hne' h
  simp only [caspTree, EvTree.AllSeq, EvTree.access_empty]
  intro succ rev
  obtain ⟨s, hs⟩ := succ
  obtain ⟨r, hr⟩ := rev
  by_cases h1 : (mem.finalVal { addr := addr, bytes := w.bytes }).setWidth w.bits = cmp1 <;>
  by_cases h2 : (mem.finalVal { addr := addr + w.bytesv, bytes := w.bytes }).setWidth w.bits = cmp2 <;>
  rcases s with _ | _ | s <;> rcases r with _ | _ | r <;> (try omega) <;>
    simp [EvTree.AllSeq, Memory.finalVal_append, hne, hne', h1, h2] at h ⊢
  all_goals first | exact hret _ _ _ h | exact hret _ _ _ h.1 | exact hret _ _ _ h.2

/-- `AllMem` is a precondition for the sequential runs of the translated
event tree, with no declarations (every access its own footprint). -/
theorem _root_.Effects.allMem_sound {tid : Nat} {Q : MachineState → Memory → Prop} (e : Effects) :
    ∀ (mem : Memory), e.AllMem tid mem Q → (toEv {} e).AllSeq tid mem Q := by
  induction e with
  | done a => intro mem h; exact h
  | unimplemented msg => intro mem h; exact h.elim
  | unaligned_sp sp => intro mem h; exact h.elim
  | nonmem_load dmem addr w ret ih => intro mem h; exact ih _ _ mem h
  | nonmem_store dmem addr v ret ih => intro mem h; exact ⟨ih _ _ h, fun h => nomatch h⟩
  | sync_load k xcl dmem addr w ret ih => intro mem h; exact ih _ _ mem h
  | sync_store k xcl dmem addr v ret ih => intro mem h; exact ⟨ih _ _ _ h.1, fun hx => ih _ _ _ (h.2 hx)⟩
  | rmw k noRet dmem addr w op ret ih =>
    intro mem h
    simp only [Effects.AllMem, loc] at h
    simp only [toEv, EvTree.access_empty, EvTree.AllSeq, Option.map]
    split at h <;> rename_i hop <;> simp only [hop] <;> exact ih _ _ _ h
  | sync_load_pair k xcl dmem addr w ret ih =>
    intro mem h
    simp only [toEv, pairIsOneLoc, List.any_nil, Bool.false_eq_true, ite_false, EvTree.access_empty,
      EvTree.AllSeq]
    exact ih _ _ _ mem h
  | sync_store_pair k xcl dmem addr v1 v2 ret ih =>
    intro mem h
    simp only [toEv, pairIsOneLoc, List.any_nil, Bool.false_eq_true, ite_false, EvTree.access_empty,
      EvTree.AllSeq, ite_true]
    exact ⟨⟨ih _ _ _ h.1, fun h => nomatch h⟩, fun hx => ih _ _ _ (h.2 hx)⟩
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    intro mem h
    exact caspTree_allSeq (P := fun o1 o2 mem => (ret o1 o2 dmem).AllMem tid mem Q)
      (fun o1 o2 mem h => ih o1 o2 dmem mem h) h
  | fence k ok ih => intro mem h; exact ih () mem h
  | @undefined α inst ret ih =>
    intro mem h
    cases inst with
    | bool => exact fun i => ih _ mem (h _)
    | bitvec w => trivial
    | statusFlags => trivial
  | require_read_access addr w ok ih => intro mem h; exact ih () mem h
  | require_write_access addr w ok ih => intro mem h; exact ih () mem h
  | require_exec_access p ok ih => intro mem h; exact ih () mem h

/-! ## The merged run: `All` with the access discipline -/

/-- `Effects.All post`, with every data access required to respect the layout
`L` (`SharedLayout.Ok`). -/
def _root_.Effects.AllW (L : SharedLayout) (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .unaligned_sp _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | .sync_load .. => False
  | .sync_store .. => False
  | .rmw .. => False
  | .sync_load_pair .. => False
  | .sync_store_pair .. => False
  | .rmw_pair .. => False
  | .fence _ ok => (ok ()).AllW L post
  | @Effects.undefined α _ ret => ∀ v : α, (ret v).AllW L post
  | .require_read_access addr w ok => L.Ok addr w.bytes ∧ (ok ()).AllW L post
  | .require_write_access addr w ok => L.Ok addr w.bytes ∧ (ok ()).AllW L post
  | .require_exec_access _ ok => (ok ()).AllW L post

/-- `AllW` is `All` together with the access discipline. -/
theorem _root_.Effects.allW_iff (L : SharedLayout) (post : MachineState → Prop) (e : Effects) :
    e.AllW L post ↔ e.All post ∧ e.AllW L (fun _ => True) := by
  induction e with
  | done a => simp [Effects.AllW, Effects.All]
  | fence k ok ih => exact ih ()
  | @undefined α inst ret ih =>
    simp only [Effects.AllW, Effects.All]
    exact ⟨fun h => ⟨fun v => ((ih v).mp (h v)).1, fun v => ((ih v).mp (h v)).2⟩,
      fun h v => (ih v).mpr ⟨h.1 v, h.2 v⟩⟩
  | require_read_access addr w ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨h1, h2, h3⟩⟩
  | require_write_access addr w ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨h1, h2, h3⟩⟩
  | require_exec_access p ok ih => exact ih ()
  | _ => simp [Effects.AllW, Effects.All]

/-- Without shared locations the discipline is empty. -/
theorem _root_.Effects.allW_nil (post : MachineState → Prop) (e : Effects) : e.AllW [] post ↔ e.All post := by
  induction e with
  | done a => rfl
  | fence k ok ih => exact ih ()
  | @undefined α inst ret ih => exact forall_congr' ih
  | require_read_access addr w ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun h => h.2, fun h => ⟨SharedLayout.ok_nil _ _, h⟩⟩
  | require_write_access addr w ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun h => h.2, fun h => ⟨SharedLayout.ok_nil _ _, h⟩⟩
  | require_exec_access p ok ih => exact ih ()
  | _ => simp [Effects.AllW, Effects.All]

/-! ## The simulation, per primitive

Every lemma relates the merged state `⟨r, f, D⟩` to the split state
`⟨r, f, d⟩` (same registers and flags) under `MemRel L d m D`, and takes the
continuation hypothesis for all related states. -/

section Sim

variable {L : SharedLayout} {tid : Nat} {P : MachineState → Prop} {Q : MachineState → Memory → Prop}

theorem sharedLoc_eq (a : BitVec 64) (n : Nat) : sharedLoc a n = loc a n := rfl

private theorem bits_eq (w : MemWidth) : w.bits = 8 * w.bytes := by cases w <;> rfl

theorem load_sim {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {addr : BitVec 64}
    {w : MemWidth} {k : w.type → MachineData → Effects}
    (hk : ∀ v r f D d m, MemRel L d m D → (k v ⟨r, f, D⟩).AllW L P → (k v ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.load ⟨r, f, D⟩ addr w k).AllW L P) :
    (MachineData.load ⟨r, f, d⟩ addr w k).AllMem tid m Q := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    exact hk _ _ _ _ _ _ hrel h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨_, hD⟩ | hD
    · rw [hD] at h
      simp only at h
      rw [sharedBytes_val m addr (bits_eq w), sharedLoc_eq] at h
      exact hk _ _ _ _ _ _ hrel h
    · rw [hD] at h
      exact h.elim

theorem loadK_sim {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {lk : Kraken.LoadKind}
    {xcl : Bool} {addr : BitVec 64} {w : MemWidth} {k : w.type → MachineData → Effects}
    (hk : ∀ v r f D d m, MemRel L d m D → (k v ⟨r, f, D⟩).AllW L P → (k v ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.loadK ⟨r, f, D⟩ lk xcl addr w k).AllW L P) :
    (MachineData.loadK ⟨r, f, d⟩ lk xcl addr w k).AllMem tid m Q := by
  unfold MachineData.loadK at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    exact hk _ _ _ _ _ _ hrel h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨_, hD⟩ | hD
    · rw [hD] at h
      simp only at h
      rw [sharedBytes_val m addr (bits_eq w), sharedLoc_eq] at h
      exact hk _ _ _ _ _ _ hrel h
    · rw [hD] at h
      exact h.elim

theorem store_sim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {w : MemWidth} {v : w.type} {k : MachineData → Effects}
    (hk : ∀ r f D d m, MemRel L d m D → (k ⟨r, f, D⟩).AllW L P → (k ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.store ⟨r, f, D⟩ addr v k).AllW L P) :
    (MachineData.store ⟨r, f, d⟩ addr v k).AllMem tid m Q := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    exact hk _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
    · rw [hD] at h
      exact hk _ _ _ _ _ (hrel.store_shared hL hmem (bits_eq w) v tid) h
    · rw [hD] at h
      exact h.elim

theorem storeK_sim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {k : Bool → MachineData → Effects}
    (hk : ∀ b r f D d m, MemRel L d m D → (k b ⟨r, f, D⟩).AllW L P → (k b ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.storeK ⟨r, f, D⟩ sk xcl addr v k).AllW L P) :
    (MachineData.storeK ⟨r, f, d⟩ sk xcl addr v k).AllMem tid m Q := by
  unfold MachineData.storeK at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    have hrel' := hrel.store_priv (n := w.bytes) v.toInt (Mem.loadBytes_isSome_of_loadInt hd)
    simp only at h ⊢
    cases xcl with
    | false => exact hk _ _ _ _ _ _ hrel' h
    | true =>
      simp only [ite_true, Effects.AllW, Effects.AllMem] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ _ _ _ _ hrel' (h true)
      | false => exact hk _ _ _ _ _ _ hrel (h false)
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
    · rw [hD] at h
      have hrel' := hrel.store_shared hL hmem (bits_eq w) v tid
      simp only at h
      cases xcl with
      | false => exact ⟨hk _ _ _ _ _ _ hrel' h, fun h => nomatch h⟩
      | true =>
        simp only [ite_true, Effects.AllW] at h
        exact ⟨hk _ _ _ _ _ _ hrel' (h true), fun _ => hk _ _ _ _ _ _ hrel (h false)⟩
    · rw [hD] at h
      exact h.elim

theorem rmwK_sim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {rk : Kraken.RmwKind} {nr : Bool} {addr : BitVec 64} {w : MemWidth} {op : w.type → Option w.type}
    {k : w.type → MachineData → Effects}
    (hk : ∀ v r f D d m, MemRel L d m D → (k v ⟨r, f, D⟩).AllW L P → (k v ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.rmwK ⟨r, f, D⟩ rk nr addr w op k).AllW L P) :
    (MachineData.rmwK ⟨r, f, d⟩ rk nr addr w op k).AllMem tid m Q := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, -, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt w.bits x) with
    | some v =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ hrel h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
    · rw [hD] at h
      simp only at h
      rw [sharedBytes_val m addr (bits_eq w), sharedLoc_eq] at h
      cases hop : op ((m.finalVal (loc addr w.bytes)).setWidth w.bits) with
      | some v =>
        rw [hop] at h
        exact hk _ _ _ _ _ _ (hrel.store_shared hL hmem (bits_eq w) v tid) h
      | none =>
        rw [hop] at h
        exact hk _ _ _ _ _ _ hrel h
    · rw [hD] at h
      exact h.elim

/-- A load of a shared location of the merged memory, at the width of the location. -/
private theorem shared_load_val (m : Memory) (addr : BitVec 64) (w : MemWidth) :
    (BitVec.ofInt w.bits (Int.ofBytes (sharedBytes m addr w.bytes)) : w.type) =
      (m.finalVal (loc addr w.bytes)).setWidth w.bits := by
  rw [sharedBytes_val m addr (bits_eq w), sharedLoc_eq]

theorem loadPairK_sim {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {lk : Kraken.LoadKind}
    {xcl : Bool} {addr : BitVec 64} {w : MemWidth} {k : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ r f D d m, MemRel L d m D → (k v₁ v₂ ⟨r, f, D⟩).AllW L P → (k v₁ v₂ ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.loadPairK ⟨r, f, D⟩ lk xcl addr w k).AllW L P) :
    (MachineData.loadPairK ⟨r, f, d⟩ lk xcl addr w k).AllMem tid m Q := by
  unfold MachineData.loadPairK at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok₁, hok₂, h⟩ := h
  cases hd₁ : Mem.loadInt d addr w.bytes with
  | some x₁ =>
    rw [hrel.loadInt_priv hd₁] at h
    cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes with
    | some x₂ =>
      rw [hrel.loadInt_priv hd₂] at h
      exact hk _ _ _ _ _ _ _ hrel h
    | none =>
      simp only [Effects.AllMem]
      rcases hrel.loadInt_none hd₂ hok₂ with ⟨_, hD₂⟩ | hD₂ <;> rw [hD₂] at h <;> simp only [Effects.AllW] at h
      · simp only [shared_load_val] at h
        exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    rcases hrel.loadInt_none hd₁ hok₁ with ⟨_, hD₁⟩ | hD₁ <;> rw [hD₁] at h
    · cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes with
      | some x₂ =>
        rw [hrel.loadInt_priv hd₂] at h
        simp only [Effects.AllMem]
        simp only [shared_load_val] at h
        exact hk _ _ _ _ _ _ _ hrel h
      | none =>
        simp only [Effects.AllMem]
        rcases hrel.loadInt_none hd₂ hok₂ with ⟨_, hD₂⟩ | hD₂ <;> rw [hD₂] at h <;> simp only [Effects.AllW] at h
        · simp only [shared_load_val] at h
          exact hk _ _ _ _ _ _ _ hrel h
    · cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes <;>
        cases hD₂ : Mem.loadInt D (addr + w.bytesv) w.bytes <;> simp only [hD₂, Effects.AllW] at h

theorem storePairK_sim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth} {v₁ v₂ : w.type}
    {k : Bool → MachineData → Effects}
    (hk : ∀ b r f D d m, MemRel L d m D → (k b ⟨r, f, D⟩).AllW L P → (k b ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.storePairK ⟨r, f, D⟩ sk xcl addr v₁ v₂ k).AllW L P) :
    (MachineData.storePairK ⟨r, f, d⟩ sk xcl addr v₁ v₂ k).AllMem tid m Q := by
  unfold MachineData.storePairK at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok₁, hok₂, h⟩ := h
  cases hd₁ : Mem.loadInt d addr w.bytes with
  | some x₁ =>
    rw [hrel.loadInt_priv hd₁] at h
    have hb₁ := Mem.loadBytes_isSome_of_loadInt hd₁
    have hrel₁ := hrel.store_priv (n := w.bytes) v₁.toInt hb₁
    cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes with
    | some x₂ =>
      rw [hrel.loadInt_priv hd₂] at h
      have hrel₂ := hrel₁.store_priv (n := w.bytes) v₂.toInt
        (Mem.loadBytes_isSome_storeBytes _ _ (Mem.loadBytes_isSome_of_loadInt hd₂))
      simp only at h ⊢
      cases xcl with
      | false => exact hk _ _ _ _ _ _ hrel₂ h
      | true =>
        simp only [ite_true, Effects.AllW, Effects.AllMem] at h ⊢
        intro b
        cases b with
        | true => exact hk _ _ _ _ _ _ hrel₂ (h true)
        | false => exact hk _ _ _ _ _ _ hrel (h false)
    | none =>
      simp only [Effects.AllMem]
      rcases hrel.loadInt_none hd₂ hok₂ with ⟨hmem₂, hD₂⟩ | hD₂ <;> rw [hD₂] at h <;> simp only [Effects.AllW] at h
      · have hrel₂ := hrel₁.store_shared hL hmem₂ (bits_eq w) v₂ tid
        simp only [ite_true, ite_false, Bool.false_eq_true]
        cases xcl with
        | false => exact ⟨hk _ _ _ _ _ _ hrel₂ h, fun h => nomatch h⟩
        | true =>
          simp only [ite_true, Effects.AllW] at h
          exact ⟨hk _ _ _ _ _ _ hrel₂ (h true), fun _ => hk _ _ _ _ _ _ hrel (h false)⟩
  | none =>
    rcases hrel.loadInt_none hd₁ hok₁ with ⟨hmem₁, hD₁⟩ | hD₁ <;> rw [hD₁] at h
    · have hrel₁ := hrel.store_shared hL hmem₁ (bits_eq w) v₁ tid
      cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes with
      | some x₂ =>
        rw [hrel.loadInt_priv hd₂] at h
        have hrel₂ := hrel₁.store_priv (n := w.bytes) v₂.toInt (Mem.loadBytes_isSome_of_loadInt hd₂)
        simp only [Effects.AllMem, ite_true, ite_false, Bool.false_eq_true]
        simp only at h
        cases xcl with
        | false => exact ⟨hk _ _ _ _ _ _ hrel₂ h, fun h => nomatch h⟩
        | true =>
          simp only [ite_true, Effects.AllW] at h
          exact ⟨hk _ _ _ _ _ _ hrel₂ (h true), fun _ => hk _ _ _ _ _ _ hrel (h false)⟩
      | none =>
        simp only [Effects.AllMem]
        rcases hrel.loadInt_none hd₂ hok₂ with ⟨hmem₂, hD₂⟩ | hD₂ <;> rw [hD₂] at h <;> simp only [Effects.AllW] at h
        · have hrel₂ := hrel₁.store_shared hL hmem₂ (bits_eq w) v₂ tid
          cases xcl with
          | false => exact ⟨hk _ _ _ _ _ _ hrel₂ h, fun h => nomatch h⟩
          | true =>
            simp only [ite_true, Effects.AllW] at h
            exact ⟨hk _ _ _ _ _ _ hrel₂ (h true), fun _ => hk _ _ _ _ _ _ hrel (h false)⟩
    · cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes <;>
        cases hD₂ : Mem.loadInt D (addr + w.bytesv) w.bytes <;> simp only [hD₂, Effects.AllW] at h

/-- `MemRel` only sees the Promising memory through the final values. -/
theorem MemRel.congr_finalVal {d D : DataMem} {m₁ m₂ : Memory} (h : MemRel L d m₁ D)
    (hfv : ∀ l, m₁.finalVal l = m₂.finalVal l) : MemRel L d m₂ D :=
  ⟨h.priv, h.split, fun a n ha => by rw [h.shared a n ha, sharedBytes, sharedBytes, hfv]⟩

/-- Appends to two different locations commute, as far as the final values go. -/
theorem finalVal_append_comm (m : Memory) {w₁ w₂ : Msg} (hne : w₁.loc ≠ w₂.loc) (l : Loc) :
    ((m.append w₁).1.append w₂).1.finalVal l = ((m.append w₂).1.append w₁).1.finalVal l := by
  simp only [Memory.finalVal_append]
  by_cases h₁ : w₁.loc = l <;> by_cases h₂ : w₂.loc = l <;> simp only [h₁, h₂, ite_true, ite_false]
  exact absurd (h₁.trans h₂.symm) hne

theorem rmwPairK_sim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {rk : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth} {c₁ c₂ n₁ n₂ : w.type}
    {k : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ r f D d m, MemRel L d m D → (k v₁ v₂ ⟨r, f, D⟩).AllW L P → (k v₁ v₂ ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.rmwPairK ⟨r, f, D⟩ rk addr c₁ c₂ n₁ n₂ k).AllW L P) :
    (MachineData.rmwPairK ⟨r, f, d⟩ rk addr c₁ c₂ n₁ n₂ k).AllMem tid m Q := by
  unfold MachineData.rmwPairK at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok₁, -, hok₂, -, h⟩ := h
  cases hd₁ : Mem.loadInt d addr w.bytes with
  | some x₁ =>
    rw [hrel.loadInt_priv hd₁] at h
    have hb₁ := Mem.loadBytes_isSome_of_loadInt hd₁
    have hrel₁ := hrel.store_priv (n := w.bytes) n₁.toInt hb₁
    cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes with
    | some x₂ =>
      rw [hrel.loadInt_priv hd₂] at h
      have hrel₂ := hrel₁.store_priv (n := w.bytes) n₂.toInt
        (Mem.loadBytes_isSome_storeBytes _ _ (Mem.loadBytes_isSome_of_loadInt hd₂))
      simp only at h ⊢
      split at h
      · rename_i hc; rw [if_pos hc]; exact hk _ _ _ _ _ _ _ hrel₂ h
      · rename_i hc; rw [if_neg hc]; exact hk _ _ _ _ _ _ _ hrel h
    | none =>
      simp only [Effects.AllMem]
      rcases hrel.loadInt_none hd₂ hok₂ with ⟨hmem₂, hD₂⟩ | hD₂ <;> rw [hD₂] at h <;> simp only [Effects.AllW] at h
      · have hrel₂ := hrel₁.store_shared hL hmem₂ (bits_eq w) n₂ tid
        simp only [shared_load_val] at h
        split at h
        · rename_i hc; simp only [hc, ite_true]; exact hk _ _ _ _ _ _ _ hrel₂ h
        · rename_i hc; simp only [hc, ite_false, Bool.false_eq_true]; exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    rcases hrel.loadInt_none hd₁ hok₁ with ⟨hmem₁, hD₁⟩ | hD₁ <;> rw [hD₁] at h
    · have hrel₁ := hrel.store_shared hL hmem₁ (bits_eq w) n₁ tid
      cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes with
      | some x₂ =>
        rw [hrel.loadInt_priv hd₂] at h
        have hrel₂ := hrel₁.store_priv (n := w.bytes) n₂.toInt (Mem.loadBytes_isSome_of_loadInt hd₂)
        simp only [Effects.AllMem]
        simp only [shared_load_val] at h
        split at h
        · rename_i hc; simp only [hc, ite_true]; exact hk _ _ _ _ _ _ _ hrel₂ h
        · rename_i hc; simp only [hc, ite_false, Bool.false_eq_true]; exact hk _ _ _ _ _ _ _ hrel h
      | none =>
        simp only [Effects.AllMem]
        rcases hrel.loadInt_none hd₂ hok₂ with ⟨hmem₂, hD₂⟩ | hD₂ <;> rw [hD₂] at h <;> simp only [Effects.AllW] at h
        · have hrel₂ := hrel₁.store_shared hL hmem₂ (bits_eq w) n₂ tid
          simp only [shared_load_val] at h
          split at h
          · rename_i hc
            simp only [hc, ite_true]
            exact ⟨hk _ _ _ _ _ _ _ hrel₂ h,
              hk _ _ _ _ _ _ _ (MemRel.congr_finalVal hrel₂ (finalVal_append_comm m (loc_pair_ne addr w))) h⟩
          · rename_i hc; simp only [hc, ite_false, Bool.false_eq_true]; exact hk _ _ _ _ _ _ _ hrel h
    · cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes <;>
        cases hD₂ : Mem.loadInt D (addr + w.bytesv) w.bytes <;> simp only [hD₂, Effects.AllW] at h

/-! ## The simulation, per addressing form -/

/-- The address and register file `AddrExpr.eval` computes: it reads and
writes registers only. -/
def _root_.AddrExpr.evalR [Labels] (a : AddrExpr) (r : Reg64s) (p : Std.Rco Int64) : BitVec 64 × Reg64s :=
  ((a.eval { regs := r } p).1, (a.eval { regs := r } p).2.regs)

theorem _root_.AddrExpr.eval_mk [Labels] (a : AddrExpr) (r : Reg64s) (f : StatusFlags) (D : DataMem)
    (p : Std.Rco Int64) : a.eval ⟨r, f, D⟩ p = ((a.evalR r p).1, ⟨(a.evalR r p).2, f, D⟩) := by
  obtain ⟨base, off⟩ := a
  cases off with
  | reg e => rfl
  | imm i =>
    obtain ⟨imm, index⟩ := i
    cases index with
    | none => rfl
    | some x => cases x <;> rfl

theorem AddrExpr.checkSPAlignment_sim {a : AddrExpr} {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {m : Memory} {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).AllW L P → (ok₂ ()).AllMem tid m Q)
    (h : (a.checkSPAlignment ⟨r, f, D⟩ ok₁).AllW L P) : (a.checkSPAlignment ⟨r, f, d⟩ ok₂).AllMem tid m Q := by
  unfold AddrExpr.checkSPAlignment at h ⊢
  generalize a.base = b at h ⊢
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk h
    | SP =>
      simp only at h ⊢
      split at h
      · exact h.elim
      · rename_i hc
        rw [ite_eq_right hc]
        exact hk h

theorem UnscaledAddrExpr.checkSPAlignment_sim {a : UnscaledAddrExpr} {r : Reg64s} {f : StatusFlags}
    {D d : DataMem} {m : Memory} {ok₁ ok₂ : Unit → Effects} (hk : (ok₁ ()).AllW L P → (ok₂ ()).AllMem tid m Q)
    (h : (a.checkSPAlignment ⟨r, f, D⟩ ok₁).AllW L P) : (a.checkSPAlignment ⟨r, f, d⟩ ok₂).AllMem tid m Q := by
  unfold UnscaledAddrExpr.checkSPAlignment at h ⊢
  generalize a.base = b at h ⊢
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk h
    | SP =>
      simp only at h ⊢
      split at h
      · exact h.elim
      · rename_i hc
        rw [ite_eq_right hc]
        exact hk h

theorem interpBase_sim {base : RegOrSp .W64} {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {ok₁ ok₂ : BitVec 64 → Effects} (hk : ∀ a, (ok₁ a).AllW L P → (ok₂ a).AllMem tid m Q)
    (h : (base.interpBase ⟨r, f, D⟩ ok₁).AllW L P) : (base.interpBase ⟨r, f, d⟩ ok₂).AllMem tid m Q := by
  unfold RegOrSp.interpBase at h ⊢
  cases base with
  | low x w' =>
    cases x with
    | reg x => exact hk _ h
    | SP =>
      simp only at h ⊢
      split at h
      · exact h.elim
      · rename_i hc
        rw [ite_eq_right hc]
        exact hk _ h

theorem AddrExpr.interpLoad_sim [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64} {r : Reg64s}
    {f : StatusFlags} {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    (hk : ∀ v r f D d m, MemRel L d m D → (k v ⟨r, f, D⟩).AllW L P → (k v ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (a.interpLoad ⟨r, f, D⟩ p k).AllW L P) :
    (a.interpLoad ⟨r, f, d⟩ p k).AllMem tid m Q := by
  unfold AddrExpr.interpLoad at h ⊢
  refine AddrExpr.checkSPAlignment_sim (fun h => ?_) h
  simp only [AddrExpr.eval_mk] at h ⊢
  exact load_sim hk hrel h

theorem AddrExpr.interpStore_sim (hL : L.WF) [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64}
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {v : w.type} {k : MachineData → Effects}
    (hk : ∀ r f D d m, MemRel L d m D → (k ⟨r, f, D⟩).AllW L P → (k ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (a.interpStore ⟨r, f, D⟩ p v k).AllW L P) :
    (a.interpStore ⟨r, f, d⟩ p v k).AllMem tid m Q := by
  unfold AddrExpr.interpStore at h ⊢
  refine AddrExpr.checkSPAlignment_sim (fun h => ?_) h
  simp only [AddrExpr.eval_mk] at h ⊢
  exact store_sim hL hk hrel h

theorem UnscaledAddrExpr.interpLoad_sim [Labels] {w : MemWidth} {a : UnscaledAddrExpr} {p : Std.Rco Int64}
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    (hk : ∀ v r f D d m, MemRel L d m D → (k v ⟨r, f, D⟩).AllW L P → (k v ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (a.interpLoad ⟨r, f, D⟩ p k).AllW L P) :
    (a.interpLoad ⟨r, f, d⟩ p k).AllMem tid m Q := by
  unfold UnscaledAddrExpr.interpLoad at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_sim (fun h => ?_) h
  exact load_sim hk hrel h

theorem UnscaledAddrExpr.interpStore_sim (hL : L.WF) [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {v : w.type}
    {k : MachineData → Effects}
    (hk : ∀ r f D d m, MemRel L d m D → (k ⟨r, f, D⟩).AllW L P → (k ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (a.interpStore ⟨r, f, D⟩ p v k).AllW L P) :
    (a.interpStore ⟨r, f, d⟩ p v k).AllMem tid m Q := by
  unfold UnscaledAddrExpr.interpStore at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_sim (fun h => ?_) h
  exact store_sim hL hk hrel h

theorem AddrOrLit.interpLoad_sim [Labels] {w : MemWidth} {a : AddrOrLit} {p : Std.Rco Int64} {r : Reg64s}
    {f : StatusFlags} {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    (hk : ∀ v r f D d m, MemRel L d m D → (k v ⟨r, f, D⟩).AllW L P → (k v ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (a.interpLoad ⟨r, f, D⟩ p k).AllW L P) :
    (a.interpLoad ⟨r, f, d⟩ p k).AllMem tid m Q := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_sim hk hrel h
  | lit l =>
    cases l with
    | addr a => exact load_sim hk hrel h
    | pool q => exact hk _ _ _ _ _ _ hrel h

/-! ## The simulation, per instruction -/

/- The dictionary lemmas are applied by search, as in `Kraken.InterpSound`:
sealing the primitives they are keyed on keeps a failed attempt a comparison of
head symbols. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK MachineData.storeK
  MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK AddrExpr.interpLoad AddrExpr.interpStore UnscaledAddrExpr.interpLoad
  UnscaledAddrExpr.interpStore AddrOrLit.interpLoad AddrExpr.checkSPAlignment RegOrSp.interpBase

set_option hygiene false in
/-- Reduce the interpreter on both sides and apply the dictionary until the
continuation hypotheses `hk`/`hj` close every leaf. -/
local macro "sim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllW,
      Effects.AllMem, AddrExpr.eval_mk] at h ⊢ <;>
    repeat' first
      | exact hk _ _ _ _ _ hrel h
      | exact hj _ _ _ _ _ _ hrel h
      | exact h.elim
      | refine AddrOrLit.interpLoad_sim (fun v r f D d m hrel h => ?_) hrel h
      | refine AddrExpr.interpLoad_sim (fun v r f D d m hrel h => ?_) hrel h
      | refine UnscaledAddrExpr.interpLoad_sim (fun v r f D d m hrel h => ?_) hrel h
      | refine AddrExpr.interpStore_sim hL (fun r f D d m hrel h => ?_) hrel h
      | refine UnscaledAddrExpr.interpStore_sim hL (fun r f D d m hrel h => ?_) hrel h
      | refine AddrExpr.checkSPAlignment_sim (fun h => ?_) h
      | refine load_sim (fun v r f D d m hrel h => ?_) hrel h
      | refine store_sim hL (fun r f D d m hrel h => ?_) hrel h
      | refine loadK_sim (fun v r f D d m hrel h => ?_) hrel h
      | refine storeK_sim hL (fun b r f D d m hrel h => ?_) hrel h
      | refine rmwK_sim hL (fun v r f D d m hrel h => ?_) hrel h
      | refine loadPairK_sim (fun v₁ v₂ r f D d m hrel h => ?_) hrel h
      | refine storePairK_sim hL (fun b r f D d m hrel h => ?_) hrel h
      | refine rmwPairK_sim hL (fun v₁ v₂ r f D d m hrel h => ?_) hrel h
      | refine interpBase_sim (fun a h => ?_) h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllW, Effects.AllMem,
          AddrExpr.eval_mk] at h ⊢))

theorem operation_sim (hL : L.WF) [Labels] {w : RegWidth} (op : Operation w) (p : Std.Rco Int64)
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : MachineData → Effects}
    {j : Int64 → MachineData → Effects}
    (hk : ∀ r f D d m, MemRel L d m D → (k ⟨r, f, D⟩).AllW L P → (k ⟨r, f, d⟩).AllMem tid m Q)
    (hj : ∀ pc r f D d m, MemRel L d m D → (j pc ⟨r, f, D⟩).AllW L P → (j pc ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (Operation.interp op p ⟨r, f, D⟩ k j).AllW L P) :
    (Operation.interp op p ⟨r, f, d⟩ k j).AllMem tid m Q := by
  cases op <;> sim_search

theorem instr_sim (hL : L.WF) [Labels] (i : Instr) (p : Std.Rco Int64)
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : MachineData → Effects}
    {j : Int64 → MachineData → Effects}
    (hk : ∀ r f D d m, MemRel L d m D → (k ⟨r, f, D⟩).AllW L P → (k ⟨r, f, d⟩).AllMem tid m Q)
    (hj : ∀ pc r f D d m, MemRel L d m D → (j pc ⟨r, f, D⟩).AllW L P → (j pc ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (i.interp ⟨r, f, D⟩ p k j).AllW L P) :
    (i.interp ⟨r, f, d⟩ p k j).AllMem tid m Q := by
  unfold Instr.interp at h ⊢
  exact operation_sim hL _ _ hk hj hrel h

theorem directive_sim (hL : L.WF) [Labels] (dir : Directive) (p : Std.Rco Int64)
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : MachineData → Effects}
    {j : Int64 → MachineData → Effects}
    (hk : ∀ r f D d m, MemRel L d m D → (k ⟨r, f, D⟩).AllW L P → (k ⟨r, f, d⟩).AllMem tid m Q)
    (hj : ∀ pc r f D d m, MemRel L d m D → (j pc ⟨r, f, D⟩).AllW L P → (j pc ⟨r, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (dir.interp ⟨r, f, D⟩ p k j).AllW L P) :
    (dir.interp ⟨r, f, d⟩ p k j).AllMem tid m Q := by
  cases dir with
  | instr i => exact instr_sim hL i p hk hj hrel h
  | label l => exact hk _ _ _ _ _ hrel h
  | byteArray b => exact h.elim

theorem directives_sim (hL : L.WF) [Labels] (ds : List (Directive × Nat)) :
    ∀ (pc : Int64) {r : Reg64s} {f : StatusFlags} {D d : DataMem} {m : Memory}
      {ret : Int64 → MachineData → Effects},
      (∀ pc r f D d m, MemRel L d m D → (ret pc ⟨r, f, D⟩).AllW L P → (ret pc ⟨r, f, d⟩).AllMem tid m Q) →
      MemRel L d m D → (Directives.interp ds ⟨r, f, D⟩ pc ret).AllW L P →
        (Directives.interp ds ⟨r, f, d⟩ pc ret).AllMem tid m Q := by
  induction ds with
  | nil => intro pc r f D d m ret hret hrel h; exact hret _ _ _ _ _ _ hrel h
  | cons x ds ih =>
    intro pc r f D d m ret hret hrel h
    obtain ⟨dir, sz⟩ := x
    simp only [Directives.interp] at h ⊢
    exact directive_sim hL dir _ (fun r f D d m hrel h => ih _ hret hrel h) hret hrel h

/-- One instruction, merged under `AllW`, split under `AllMem`: the split run
ends related to a merged state the merged run allows. -/
theorem step_sim (hL : L.WF) (e : _root_.Executable) {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {m : Memory} {pc : Int64}
    (hQ : ∀ r f D d m pc, MemRel L d m D → P (⟨r, f, D⟩, pc) → Q (⟨r, f, d⟩, pc) m)
    (hrel : MemRel L d m D) (h : (Executable.step e (⟨r, f, D⟩, pc) .done).AllW L P) :
    (Executable.step e (⟨r, f, d⟩, pc) .done).AllMem tid m Q := by
  unfold Executable.step at h ⊢
  letI := Executable.labels e
  exact directives_sim hL _ _ (fun pc r f D d m hrel h => hQ r f D d m pc hrel h) hrel h

end Sim

/-! ## Promise-free runs -/

/-- One instruction of `e` under `AllW`: the step relation of the merged
judgment. -/
def step1W (L : SharedLayout) (e : _root_.Executable) (s : MachineState) (post : MachineState → Prop) : Prop :=
  (Executable.step e s .done).AllW L post

theorem step1W_iff [_root_.Layout] (L : SharedLayout) (e : _root_.Executable) (s : MachineState)
    (post : MachineState → Prop) :
    step1W L e s post ↔ step1 e s post ∧ (Executable.step e s .done).AllW L (fun _ => True) :=
  Effects.allW_iff L post _

theorem step1W_nil [_root_.Layout] (e : _root_.Executable) (s : MachineState) (post : MachineState → Prop) :
    step1W [] e s post ↔ step1 e s post :=
  Effects.allW_nil post _

/-- Without shared locations, Kraken's judgment is the merged one. -/
theorem eventually_step1W_nil [_root_.Layout] {e : _root_.Executable} {P : MachineState → Prop}
    {s₀ : MachineState} (h : Eventually (step1 e) P s₀) : Eventually (step1W [] e) P s₀ := by
  induction h with
  | done s hP => exact .done s hP
  | step s mid hT _ ih => exact .step s mid ((step1W_nil e s mid).mpr hT) ih

/-- An `Eventually (step1 e)` judgment whose steps respect the layout, by an
invariant: `Inv` is preserved by every step taken, and every step from an
`Inv` state respects `L`. -/
theorem eventually_step1W [_root_.Layout] {L : SharedLayout} {e : _root_.Executable}
    {Inv P : MachineState → Prop}
    (hpres : ∀ s R, Inv s → step1 e s R → step1 e s (fun s' => R s' ∧ Inv s'))
    (hacc : ∀ s, Inv s → (Executable.step e s .done).AllW L (fun _ => True))
    {s₀ : MachineState} (h : Eventually (step1 e) P s₀) (h0 : Inv s₀) : Eventually (step1W L e) P s₀ := by
  induction h with
  | done s hP => exact .done s hP
  | step s mid hT _ ih =>
    exact .step s (fun s' => mid s' ∧ Inv s') ((step1W_iff L e s _).mpr ⟨hpres s mid h0 hT, hacc s h0⟩)
      fun s' hs' => ih s' hs'.1 hs'.2

/-- The thread state `x` on the Promising memory `m` is the merged state `y`:
the thread runs `e` and halts at `endPc`, registers, flags and pc agree,
`y`'s memory is the merge of `x`'s private memory and `m`, and the thread has
no declarations (every access is its own footprint, so the shared locations
are `sharedLoc`s). -/
def MergedRel (L : SharedLayout) (e : _root_.Executable) (endPc : Int64) (x : State × Memory) (y : MachineState) : Prop :=
  x.1.exe = e ∧ x.1.endPc = endPc ∧ x.1.st.1.regs = y.1.regs ∧ x.1.st.1.status = y.1.status ∧
    x.1.st.2 = y.2 ∧ MemRel L x.1.st.1.dmem x.2 y.1.dmem ∧ x.1.decls = {}

/-- The merged judgment simulates the sequential runs of the thread. -/
theorem seqSim_merged {L : SharedLayout} (hL : L.WF) (e : _root_.Executable) (endPc : Int64) (tid : Nat) :
    SeqSim isa tid (MergedRel L e endPc) (step1W L e) := by
  intro x y R hxy hT tree hex
  obtain ⟨⟨exe, endPc', ⟨⟨r, f, d⟩, pc⟩, showPc, decls⟩, m⟩ := x
  obtain ⟨⟨r', f', D⟩, pc'⟩ := y
  obtain ⟨he, hend, hr, hf, hpc, hrel, hds⟩ := hxy
  simp only at he hend hr hf hpc hrel hds
  subst he hend hr hf hpc hds
  simp only [isa, exec] at hex
  split at hex
  · cases hex
  · cases hex
    refine (EvTree.allSeq_map tid _ _ m _).mpr ?_
    exact Effects.allMem_sound _ m
      (step_sim hL _ (fun r f D d m pc hrel hP => ⟨(⟨r, f, D⟩, pc), ⟨rfl, rfl, rfl, rfl, rfl, hrel, rfl⟩, hP⟩) hrel hT)

/-- Conservativity for Kraken's judgment on AArch64. A judgment
`Eventually (step1W L e) P` about the merged state `(⟨r, f, D⟩, pc)` carries
over to every promise-free run of the one-thread machine whose thread runs `e`
from `(⟨r, f, d⟩, pc)` on a memory `mem` without messages, `D` being the merge
of `d` and `mem`: the run met `P` on the way (at a state whose merge satisfies
it), or the judgment still holds of the merge of where it is. -/
theorem merged_link {L : SharedLayout} (hL : L.WF) (A : Arch) (fuel : Nat) {e : _root_.Executable}
    {endPc : Int64} {showPc : Int64 → String} {r : Reg64s} {f : StatusFlags} {d D : DataMem}
    {pc : Int64} {mem : Memory} (hm : mem.msgs = #[]) (hrel : MemRel L d mem D) {P : MachineState → Prop}
    (hev : Eventually (step1W L e) P (⟨r, f, D⟩, pc)) {c : Config isa}
    (hc : ReachablePF A fuel ⟨#[Thread.init ({ exe := e, endPc, st := (⟨r, f, d⟩, pc), showPc } : State)], mem⟩ c) :
    ∃ t', c.threads = #[t'] ∧
      ((∃ z y', SeqReach 0 (({ exe := e, endPc, st := (⟨r, f, d⟩, pc), showPc } : State), mem) z ∧
          SeqReach 0 z (t'.st, c.mem) ∧ MergedRel L e endPc z y' ∧ P y') ∨
        ∃ y', MergedRel L e endPc (t'.st, c.mem) y' ∧ Eventually (step1W L e) P y') :=
  reachablePF_sim A fuel (seqSim_merged hL e endPc 0) hm (y := (⟨r, f, D⟩, pc)) ⟨rfl, rfl, rfl, rfl, rfl, hrel, rfl⟩
    hev hc

/-- A sequential run from a halted thread is empty. -/
theorem SeqReach.halted {tid : Nat} {s : State} {m : Memory} {p : State × Memory}
    (hh : isa.exec s = none) (h : SeqReach (I := isa) tid (s, m) p) : p = (s, m) := by
  cases h with
  | refl => rfl
  | step hex _ _ => rw [hh] at hex; cases hex

/-- An `Eventually` judgment at a state where every step stutters holds now. -/
theorem eventually_stutter {β : Type} {T : β → (β → Prop) → Prop} {P : β → Prop} {y : β}
    (h : Eventually T P y) : (∀ R, T y R → R y) → P y := by
  induction h with
  | done y hP => exact fun _ => hP
  | step y mid hT _ ih => exact fun hs => ih y (hs mid hT) hs

theorem MergedRel.post {L : SharedLayout} {e : _root_.Executable} {endPc : Int64} {x : State × Memory}
    {y : MachineState} {P : MachineState → Prop} (h : MergedRel L e endPc x y) (hP : P y) :
    ∃ D', MemRel L x.1.st.1.dmem x.2 D' ∧ P (⟨x.1.st.1.regs, x.1.st.1.status, D'⟩, x.1.st.2) := by
  obtain ⟨⟨r, f, D⟩, pc⟩ := y
  obtain ⟨-, -, hr, hf, hpc, hrel, -⟩ := h
  refine ⟨D, hrel, ?_⟩
  simp only at hr hf hpc
  rw [hr, hf, hpc]
  exact hP

/-- Halting runs: when `P` holds only at `endPc` and a step there changes
nothing (`hstop`: nothing is laid out at `endPc`, or what is there faults), a
promise-free run whose thread has reached `endPc` ends in a state whose merge
satisfies `P`. -/
theorem merged_link_halt {L : SharedLayout} (hL : L.WF) (A : Arch) (fuel : Nat) {e : _root_.Executable}
    {endPc : Int64} {showPc : Int64 → String} {r : Reg64s} {f : StatusFlags} {d D : DataMem}
    {pc : Int64} {mem : Memory} (hm : mem.msgs = #[]) (hrel : MemRel L d mem D) {P : MachineState → Prop}
    (hP : ∀ y, P y → y.2 = endPc) (hstop : ∀ y R, y.2 = endPc → step1W L e y R → R y)
    (hev : Eventually (step1W L e) P (⟨r, f, D⟩, pc)) {c : Config isa}
    (hc : ReachablePF A fuel ⟨#[Thread.init ({ exe := e, endPc, st := (⟨r, f, d⟩, pc), showPc } : State)], mem⟩ c)
    {t' : Thread isa} (ht : c.threads = #[t']) (hend : t'.st.st.2 = endPc) :
    ∃ D', MemRel L t'.st.st.1.dmem c.mem D' ∧ P (⟨t'.st.st.1.regs, t'.st.st.1.status, D'⟩, endPc) := by
  obtain ⟨t'', ht'', hcase⟩ := merged_link hL A fuel hm hrel hev hc
  rw [ht] at ht''
  have htt : t' = t'' := by simpa using ht''
  subst htt
  rw [← hend]
  rcases hcase with ⟨⟨z₁, z₂⟩, y', -, hz, hzy, hPy⟩ | ⟨y', hy, hev'⟩
  · -- `P` was met at `z`, which is at `endPc`, so the thread halted there
    have hpcz : z₁.st.2 = endPc := hzy.2.2.2.2.1.trans (hP y' hPy)
    have hez : z₁.endPc = endPc := hzy.2.1
    have hhalt : isa.exec z₁ = none := by
      simp [isa, exec, hpcz, hez]
    obtain ⟨h1, h2⟩ := Prod.mk.inj (SeqReach.halted hhalt hz)
    subst h1 h2
    exact hzy.post hPy
  · have hpy : y'.2 = endPc := hy.2.2.2.2.1.symm.trans hend
    exact hy.post (eventually_stutter hev' fun R hR => hstop y' R hpy hR)

end Kraken.Promising.AArch64
