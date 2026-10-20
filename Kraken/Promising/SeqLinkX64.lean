/-
Conservativity for x64: Kraken's single-threaded judgment carries over to
promise-free runs of the Promising machine (`Kraken.Promising.SeqLink`).

The shape is that of `Kraken.Promising.SeqLinkAArch64`, which see: a thread of
the Promising machine runs `Executable.step` on its private `dmem`, Kraken's
judgment is about the *merged* memory that has the shared locations mapped
(`Kraken.Promising.MergedMem`), and the link is a simulation of the split run
by the merged one, instruction by instruction:

- `Effects.AllMem tid mem Q`: the split tree, its unmapped accesses served
  sequentially by the Promising memory `mem` (`allMem_sound`).
- `Effects.AllW L P`: `Effects.All P` with every access respecting the layout
  `L` of shared locations (`allW_iff`, `allW_nil`).
- `step_sim`: one `Executable.step`, per primitive (`load_sim`, `store_sim`,
  `rmwK_sim`, `rmw_sim`, ...) and by one search over the instruction set
  (`operation_sim`).
- `merged_link`, `merged_link_halt`: an `Eventually (step1W L e) P` judgment
  about the merged state carries over to every promise-free run of the
  one-thread machine.

Vector (SSE/AVX) instructions are covered.
`toEv` splits a vector access as the memory model says (one 16-byte event if it is
guaranteed atomic, else 8-byte pieces), and `AllW` asks that the access
respect the layout as split (`SharedLayout.AvxOk`): a guaranteed-atomic access
is exactly a 16-byte location or misses the footprint, and each piece of any
other access is exactly an 8-byte location or misses it. Shared locations may
be up to 16 bytes wide (`SharedLayout.WF`).

`Kraken.Promising.SeqLinkX64Step` takes `MachineWP`'s `Eventually e.instrStep`
judgments to `step1W`. Kraken's kstep proofs conclude `Eventually
(straightlineStep e)`, a judgment over segment bursts; carrying those over is
not done.
-/
import Kraken.Promising.X64
import Kraken.Promising.SeqLink
import Kraken.Promising.MergedMem
import Kraken.X64.OmniSemantics

open Std

namespace Kraken.Promising.X64

/-! ## The split run: unmapped accesses against the Promising memory -/

/-- `loadPieces` against the Promising memory `mem`, as `seqRun` serves it:
`k` holds of the bytes read (a piece that crosses a cache line faults, which
has no run). -/
def loadPiecesMem (dmem : DataMem) (mem : Memory) (addr : BitVec 64) : Nat → (List UInt8 → Prop) → Prop
  | 0, k => k []
  | n + 1, k =>
    let rest (bs : List UInt8) : Prop := loadPiecesMem dmem mem (addr + 8) n fun bs' => k (bs ++ bs')
    match dmem.loadBytes addr 8 with
    | some bs => rest bs
    | none => if crossesLine addr then True else rest (Int.toBytes 8 ((mem.finalVal (loc addr 8)).toNat : Int))

/-- `storePieces` against the Promising memory `mem`: `k` holds of the
private memory and the Promising memory after it. -/
def storePiecesMem (tid : Nat) (addr : BitVec 64) :
    Nat → List UInt8 → DataMem → Memory → (DataMem → Memory → Prop) → Prop
  | 0, _, dmem, mem, k => k dmem mem
  | n + 1, bs, dmem, mem, k =>
    match dmem.loadBytes addr 8 with
    | some _ => storePiecesMem tid (addr + 8) n (bs.drop 8) (dmem.storeBytes addr (bs.take 8)) mem k
    | none =>
      if crossesLine addr then True
      else storePiecesMem tid (addr + 8) n (bs.drop 8) dmem
        (mem.append { loc := loc addr 8, val := (pieceVal (bs.take 8)).setWidth 128, tid }).1 k

/-- Every run of the tree, with the accesses outside `dmem` served
sequentially by the Promising memory `mem` (as `seqRun` serves them), ends in
a state and memory satisfying `Q`. Total, like `Effects.All`. -/
def _root_.Effects.AllMem (tid : Nat) (mem : Memory) (Q : MachineState → Memory → Prop) : Effects → Prop
  | .done a => Q a mem
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load dmem addr w ret => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid mem Q
  | @Effects.nonmem_store dmem addr w v ret =>
    (ret dmem).AllMem tid (mem.append { loc := loc addr w.bytes, val := v.setWidth 128, tid }).1 Q
  | @Effects.undefined α _ ret => ∀ v : α, (ret v).AllMem tid mem Q
  | .require_read_access _ _ ok => (ok ()).AllMem tid mem Q
  | .require_write_access _ _ ok => (ok ()).AllMem tid mem Q
  | .require_exec_access _ ok => (ok ()).AllMem tid mem Q
  | .sync_load _ _ dmem addr w ret => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid mem Q
  | @Effects.sync_store _ xcl dmem addr w v ret =>
    (ret true dmem).AllMem tid (mem.append { loc := loc addr w.bytes, val := v.setWidth 128, tid }).1 Q ∧
      (xcl = true → (ret false dmem).AllMem tid mem Q)
  | .rmw _ dmem addr w op ret =>
    match op ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) with
    | some v => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid
        (mem.append { loc := loc addr w.bytes, val := v.setWidth 128, tid }).1 Q
    | none => (ret ((mem.finalVal (loc addr w.bytes)).setWidth w.bits) dmem).AllMem tid mem Q
  | .fence _ ok => (ok ()).AllMem tid mem Q
  | .require_read_access_avx _ _ _ ok => (ok ()).AllMem tid mem Q
  | .require_write_access_avx _ _ _ ok => (ok ()).AllMem tid mem Q
  -- As `toEv` translates them.
  | .nonmem_load_avx atomic dmem addr w ret =>
    if atomic && w == .W128 then
      (ret ((mem.finalVal (loc addr 16)).setWidth w.bits) dmem).AllMem tid mem Q
    else
      loadPiecesMem dmem mem addr (w.bytes / 8) fun bs =>
        (ret (BitVec.ofInt w.bits (Int.ofBytes bs)) dmem).AllMem tid mem Q
  | @Effects.nonmem_store_avx atomic dmem addr w v ret =>
    if atomic && w == .W128 then
      (ret dmem).AllMem tid (mem.append { loc := loc addr 16, val := v.setWidth 128, tid }).1 Q
    else
      storePiecesMem tid addr (w.bytes / 8) (Int.toBytes w.bytes v.toInt) dmem mem fun dmem mem =>
        (ret dmem).AllMem tid mem Q
  | .rmw16 _ dmem addr op ret =>
    match op (mem.finalVal (loc addr 16)) with
    | some v => (ret (mem.finalVal (loc addr 16)) dmem).AllMem tid
        (mem.append { loc := loc addr 16, val := v, tid }).1 Q
    | none => (ret (mem.finalVal (loc addr 16)) dmem).AllMem tid mem Q

theorem loadPiecesMem_sound {σ : Type} {tid : Nat} {Q : σ → Memory → Prop} (dmem : DataMem) (mem : Memory) :
    ∀ (n : Nat) (addr : BitVec 64) (K : List UInt8 → Prop) (k : List UInt8 → EvTree σ),
      (∀ bs, K bs → (k bs).AllSeq tid mem Q) → loadPiecesMem dmem mem addr n K →
        (loadPieces {} dmem addr n k).AllSeq tid mem Q := by
  intro n
  induction n with
  | zero => intro addr K k hk h; exact hk _ h
  | succ n ih =>
    intro addr K k hk h
    dsimp only [loadPiecesMem, loadPieces] at h ⊢
    cases hbs : dmem.loadBytes addr 8 with
    | some bs =>
      rw [hbs] at h
      exact ih _ _ _ (fun bs' h' => hk _ h') h
    | none =>
      rw [hbs] at h
      dsimp only at h ⊢
      cases hc : crossesLine addr
      · simp only [hc, Bool.false_eq_true, ite_false] at h ⊢
        exact ih _ _ _ (fun bs' h' => hk _ h') h
      · simp only [hc, ite_true, EvTree.AllSeq]

theorem storePiecesMem_sound {σ : Type} {tid : Nat} {Q : σ → Memory → Prop} :
    ∀ (n : Nat) (addr : BitVec 64) (bs : List UInt8) (dmem : DataMem) (mem : Memory)
      (K : DataMem → Memory → Prop) (k : DataMem → EvTree σ),
      (∀ d m, K d m → (k d).AllSeq tid m Q) → storePiecesMem tid addr n bs dmem mem K →
        (storePieces {} addr n bs dmem k).AllSeq tid mem Q := by
  intro n
  induction n with
  | zero => intro addr bs dmem mem K k hk h; exact hk _ _ h
  | succ n ih =>
    intro addr bs dmem mem K k hk h
    dsimp only [storePiecesMem, storePieces] at h ⊢
    cases hbs : dmem.loadBytes addr 8 with
    | some bs' =>
      rw [hbs] at h
      exact ih _ _ _ _ _ _ hk h
    | none =>
      rw [hbs] at h
      dsimp only at h ⊢
      cases hc : crossesLine addr
      · simp only [hc, Bool.false_eq_true, ite_false] at h ⊢
        exact ⟨ih _ _ _ _ _ _ hk h, fun h => nomatch h⟩
      · simp only [hc, ite_true, EvTree.AllSeq]

/-- `AllMem` is a precondition for the sequential runs of the translated
event tree, with no declarations (every access its own footprint). -/
theorem _root_.Effects.allMem_sound {tid : Nat} {Q : MachineState → Memory → Prop} (e : Effects) :
    ∀ (mem : Memory), e.AllMem tid mem Q → (toEv {} e).AllSeq tid mem Q := by
  induction e with
  | done a => intro mem h; exact h
  | unimplemented msg => intro mem h; exact h.elim
  | gp_unaligned addr w => intro mem h; exact h.elim
  | nonmem_load dmem addr w ret ih => intro mem h; exact ih _ _ mem h
  | nonmem_store dmem addr v ret ih => intro mem h; exact ⟨ih _ _ h, fun h => nomatch h⟩
  | @undefined α inst ret ih =>
    intro mem h
    cases inst with
    | bool => exact fun i => ih _ mem (h _)
    | bitvec w => trivial
    | avx_bitvec w => trivial
    | statusFlags => trivial
  | require_read_access addr w ok ih => intro mem h; exact ih () mem h
  | require_write_access addr w ok ih => intro mem h; exact ih () mem h
  | require_exec_access p ok ih => intro mem h; exact ih () mem h
  | sync_load k xcl dmem addr w ret ih => intro mem h; exact ih _ _ mem h
  | sync_store k xcl dmem addr v ret ih => intro mem h; exact ⟨ih _ _ _ h.1, fun hx => ih _ _ _ (h.2 hx)⟩
  | rmw k dmem addr w op ret ih =>
    intro mem h
    simp only [Effects.AllMem, loc] at h
    simp only [toEv, EvTree.access_empty, EvTree.AllSeq, Option.map]
    split at h <;> rename_i hop <;> simp only [hop] <;> exact ih _ _ _ h
  | fence k ok ih => intro mem h; exact ih () mem h
  | require_read_access_avx addr w atomic ok ih => intro mem h; exact ih () mem h
  | require_write_access_avx addr w atomic ok ih => intro mem h; exact ih () mem h
  | nonmem_load_avx atomic dmem addr w ret ih =>
    intro mem h
    simp only [Effects.AllMem] at h
    simp only [toEv]
    split
    · rename_i hat
      rw [ite_eq_left_of_eq_true _ _ (eq_true hat)] at h
      exact ih _ _ mem h
    · rename_i hat
      rw [ite_eq_right_of_eq_false _ _ (eq_false hat)] at h
      exact loadPiecesMem_sound dmem mem _ addr _ _ (fun bs h => ih _ _ mem h) h
  | nonmem_store_avx atomic dmem addr v ret ih =>
    intro mem h
    simp only [Effects.AllMem] at h
    simp only [toEv]
    split
    · rename_i hat
      rw [ite_eq_left_of_eq_true _ _ (eq_true hat)] at h
      exact ⟨ih _ _ h, fun h => nomatch h⟩
    · rename_i hat
      rw [ite_eq_right_of_eq_false _ _ (eq_false hat)] at h
      exact storePiecesMem_sound _ addr _ dmem mem _ _ (fun d m h => ih _ m h) h
  | rmw16 k dmem addr op ret ih =>
    intro mem h
    simp only [Effects.AllMem, loc] at h
    simp only [toEv, EvTree.access_empty, EvTree.AllSeq]
    split at h <;> rename_i hop <;> simp only [hop] <;> exact ih _ _ _ h

/-! ## The merged run: `All` with the access discipline -/

/-- A vector access of width `w` at `addr` respects the layout `L`, as `toEv`
translates it: a guaranteed-atomic access (`atomic` at 16 bytes,
and `rmw16`) is exactly a 16-byte location or misses the footprint; each
8-byte piece of any other access is exactly an 8-byte location or misses the
footprint. -/
def _root_.Kraken.Promising.SharedLayout.AvxOk (L : SharedLayout) (atomic : Bool) (addr : BitVec 64)
    (w : AvxWidth) : Prop :=
  if atomic && w == .W128 then L.Ok addr 16
  else ∀ i < w.bytes / 8, L.Ok (addr + BitVec.ofNat 64 (8 * i)) 8

theorem _root_.Kraken.Promising.SharedLayout.avxOk_nil (atomic : Bool) (addr : BitVec 64) (w : AvxWidth) :
    SharedLayout.AvxOk [] atomic addr w := by
  unfold SharedLayout.AvxOk
  split
  · exact SharedLayout.ok_nil _ _
  · exact fun _ _ => SharedLayout.ok_nil _ _

/-- `Effects.All post`, with every data access required to respect the layout
`L` (`SharedLayout.Ok`). -/
def _root_.Effects.AllW (L : SharedLayout) (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ ret => ∀ v : α, (ret v).AllW L post
  | .require_read_access addr w ok => L.Ok addr w.bytes ∧ (ok ()).AllW L post
  | .require_write_access addr w ok => L.Ok addr w.bytes ∧ (ok ()).AllW L post
  | .require_exec_access _ ok => (ok ()).AllW L post
  | .sync_load .. => False
  | .sync_store .. => False
  | .rmw .. => False
  | .fence _ ok => (ok ()).AllW L post
  -- A vector access respects the layout as `toEv` splits it (`AvxOk`).
  | .require_read_access_avx addr w atomic ok => L.AvxOk atomic addr w ∧ (ok ()).AllW L post
  | .require_write_access_avx addr w atomic ok => L.AvxOk atomic addr w ∧ (ok ()).AllW L post
  | .nonmem_load_avx .. => False
  | .nonmem_store_avx .. => False
  | .rmw16 .. => False

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
  | require_read_access_avx addr w atomic ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨h1, h2, h3⟩⟩
  | require_write_access_avx addr w atomic ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨h1, h2, h3⟩⟩
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
  | require_read_access_avx addr w atomic ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun h => h.2, fun h => ⟨SharedLayout.avxOk_nil _ _ _, h⟩⟩
  | require_write_access_avx addr w atomic ok ih =>
    simp only [Effects.AllW, Effects.All, ih ()]
    exact ⟨fun h => h.2, fun h => ⟨SharedLayout.avxOk_nil _ _ _, h⟩⟩
  | _ => simp [Effects.AllW, Effects.All]

theorem mem_of_mem_directivesAtAddress {e : _root_.Executable} {a : Int64} {c : Directive × Nat}
    (h : c ∈ e.directivesAtAddress a) : c ∈ e.2 := by
  obtain ⟨start, ds⟩ := e
  unfold Kraken.Executable.directivesAtAddress at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have hx' : x ∈ Kraken.Executable.withAddresses (start, ds) :=
    (List.dropWhile_suffix _).subset ((List.takeWhile_prefix _).subset hx)
  rw [← Kraken.Executable.withAddresses_map_snd ds start]
  exact List.mem_map_of_mem hx'

/-! ## The simulation, per primitive

Every lemma relates the merged state `⟨r, z, f, D⟩` to the split state
`⟨r, z, f, d⟩` (same registers, vector registers and flags) under
`MemRel L d m D`, and takes the continuation hypothesis for all related
states. -/

section Sim

variable {L : SharedLayout} {tid : Nat} {P : MachineState → Prop} {Q : MachineState → Memory → Prop}

theorem sharedLoc_eq (a : BitVec 64) (n : Nat) : sharedLoc a n = loc a n := rfl

private theorem bits_eq (w : Width) : w.bits = 8 * w.bytes := by cases w <;> rfl

theorem load_sim {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {w : Width} {k : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.load ⟨r, z, f, D⟩ addr w k).AllW L P) :
    (MachineData.load ⟨r, z, f, d⟩ addr w k).AllMem tid m Q := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨_, hD⟩ | hD
    · rw [hD] at h
      simp only at h
      rw [sharedBytes_val m addr (bits_eq w), sharedLoc_eq] at h
      exact hk _ _ _ _ _ _ _ hrel h
    · rw [hD] at h
      exact h.elim

theorem store_sim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {w : Width} {v : w.type} {k : MachineData → Effects}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.store ⟨r, z, f, D⟩ addr v k).AllW L P) :
    (MachineData.store ⟨r, z, f, d⟩ addr v k).AllMem tid m Q := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
    · rw [hD] at h
      exact hk _ _ _ _ _ _ (hrel.store_shared hL hmem (bits_eq w) v tid) h
    · rw [hD] at h
      exact h.elim

/-- `store_sim` for a non-temporal store, whose unmapped access is a `sync_store`. -/
theorem storeNT_sim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {w : Width} {v : w.type} {k : MachineData → Effects}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.storeNT ⟨r, z, f, D⟩ addr v k).AllW L P) :
    (MachineData.storeNT ⟨r, z, f, d⟩ addr v k).AllMem tid m Q := by
  unfold MachineData.storeNT at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, h⟩ := h
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
    · rw [hD] at h
      exact ⟨hk _ _ _ _ _ _ (hrel.store_shared hL hmem (bits_eq w) v tid) h, fun hx => nomatch hx⟩
    · rw [hD] at h
      exact h.elim

theorem rmwK_sim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {rk : Kraken.RmwKind} {addr : BitVec 64} {w : Width} {op : w.type → Option w.type}
    {k : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.rmwK ⟨r, z, f, D⟩ rk addr w op k).AllW L P) :
    (MachineData.rmwK ⟨r, z, f, d⟩ rk addr w op k).AllMem tid m Q := by
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
      exact hk _ _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
    · rw [hD] at h
      simp only at h
      rw [sharedBytes_val m addr (bits_eq w), sharedLoc_eq] at h
      cases hop : op ((m.finalVal (loc addr w.bytes)).setWidth w.bits) with
      | some v =>
        rw [hop] at h
        exact hk _ _ _ _ _ _ _ (hrel.store_shared hL hmem (bits_eq w) v tid) h
      | none =>
        rw [hop] at h
        exact hk _ _ _ _ _ _ _ hrel h
    · rw [hD] at h
      exact h.elim

theorem rmwPlain_sim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {w : Width} {op : w.type → Option w.type} {k : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.rmwPlain ⟨r, z, f, D⟩ addr w op k).AllW L P) :
    (MachineData.rmwPlain ⟨r, z, f, d⟩ addr w op k).AllMem tid m Q := by
  unfold MachineData.rmwPlain at h ⊢
  refine load_sim (fun v r z f D d m hrel h => ?_) hrel h
  cases hop : op v with
  | some new =>
    rw [hop] at h
    exact store_sim hL (fun r z f D d m hrel h => hk _ _ _ _ _ _ _ hrel h) hrel h
  | none =>
    rw [hop] at h
    exact hk _ _ _ _ _ _ _ hrel h

/-! ### Vector accesses -/

private theorem avx_bytes_eq (w : AvxWidth) : w.bytes = 8 * (w.bytes / 8) := by cases w <;> rfl

private theorem ok_piece_succ {L : SharedLayout} {addr : BitVec 64} {n : Nat}
    (hok : ∀ i < n + 1, L.Ok (addr + BitVec.ofNat 64 (8 * i)) 8) :
    ∀ i < n, L.Ok (addr + 8 + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  have h := hok (i + 1) (by omega)
  have he : addr + BitVec.ofNat 64 (8 * (i + 1)) = addr + 8 + BitVec.ofNat 64 (8 * i) := by
    rw [BitVec.add_assoc]
    show addr + BitVec.ofNat 64 (8 * (i + 1)) = addr + (BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i))
    rw [← BitVec.ofNat_add, show 8 + 8 * i = 8 * (i + 1) by omega]
  rwa [he] at h

private theorem ok_piece_zero {L : SharedLayout} {addr : BitVec 64} {n : Nat}
    (hok : ∀ i < n + 1, L.Ok (addr + BitVec.ofNat 64 (8 * i)) 8) : L.Ok addr 8 := by
  simpa using hok 0 (by omega)

/-- The non-atomic vector load of the merged memory, piece by piece: each
piece respects the layout, so it is served by the private memory or is a
shared location, read from the Promising memory. -/
theorem loadPiecesMem_of {d D : DataMem} {m : Memory} (hrel : MemRel L d m D) :
    ∀ (n : Nat) (addr : BitVec 64) (bs : List UInt8) (K : List UInt8 → Prop),
      (∀ i < n, L.Ok (addr + BitVec.ofNat 64 (8 * i)) 8) → D.loadBytes addr (8 * n) = some bs → K bs →
        loadPiecesMem d m addr n K := by
  intro n
  induction n with
  | zero =>
    intro addr bs K _ hD hK
    have := Mem.loadBytes_length hD
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at this
    subst this
    exact hK
  | succ n ih =>
    intro addr bs K hok hD hK
    rw [show 8 * (n + 1) = 8 + 8 * n by omega] at hD
    obtain ⟨bs₁, bs₂, h₁, h₂, rfl⟩ := Mem.loadBytes_add_some hD
    have hok' := ok_piece_succ hok
    dsimp only [loadPiecesMem]
    cases hd : d.loadBytes addr 8 with
    | some bs₁' =>
      have he : bs₁' = bs₁ := by
        rw [← hrel.loadBytes_priv (by rw [hd]; rfl), h₁] at hd
        exact (Option.some.inj hd).symm
      subst he
      exact ih (addr + 8) bs₂ _ hok' h₂ hK
    | none =>
      dsimp only
      split
      · trivial
      · rcases ok_piece_zero hok with hmem | hoff
        · rw [hrel.shared _ _ hmem] at h₁
          obtain rfl := Option.some.inj h₁
          exact ih (addr + 8) bs₂ _ hok' h₂ hK
        · rw [hrel.loadBytes_off hoff, hd] at h₁
          cases h₁

/-- The non-atomic vector store of the merged memory, piece by piece. -/
theorem storePiecesMem_of (hL : L.WF) :
    ∀ (n : Nat) (addr : BitVec 64) (bs : List UInt8) (d D : DataMem) (m : Memory)
      (K : DataMem → Memory → Prop),
      MemRel L d m D → (∀ i < n, L.Ok (addr + BitVec.ofNat 64 (8 * i)) 8) →
      (D.loadBytes addr (8 * n)).isSome → bs.length = 8 * n → 8 * n ≤ 2 ^ 64 →
      (∀ d' m', MemRel L d' m' (D.storeBytes addr bs) → K d' m') → storePiecesMem tid addr n bs d m K := by
  intro n
  induction n with
  | zero =>
    intro addr bs d D m K hrel _ _ hlen _ hK
    have : bs = [] := List.eq_nil_of_length_eq_zero hlen
    subst this
    exact hK _ _ (by rw [Mem.storeBytes_nil]; exact hrel)
  | succ n ih =>
    intro addr bs d D m K hrel hok hD hlen hbound hK
    have hlen8 : (bs.take 8).length = 8 := by simp only [List.length_take]; omega
    have hlen' : (bs.drop 8).length = 8 * n := by simp only [List.length_drop]; omega
    have hsplit : D.storeBytes addr bs =
        (D.storeBytes addr (bs.take 8)).storeBytes (addr + 8) (bs.drop 8) := by
      conv => lhs; rw [← List.take_append_drop 8 bs]
      rw [Mem.storeBytes_append _ _ _ _ (by rw [hlen8, hlen']; omega), hlen8]
      rfl
    rw [show 8 * (n + 1) = 8 + 8 * n by omega] at hD
    obtain ⟨bs', hbs'⟩ := Option.isSome_iff_exists.mp hD
    obtain ⟨bs₁, bs₂, h₁, h₂, -⟩ := Mem.loadBytes_add_some hbs'
    have hD' : ∀ D' : DataMem, ((D'.storeBytes addr (bs.take 8)).loadBytes (addr + 8) (8 * n)).isSome ∨
        D' ≠ D := fun D' => by
      by_cases hDD : D' = D
      · subst hDD; exact .inl (Mem.loadBytes_isSome_storeBytes _ _ (by rw [show addr + 8 = addr + BitVec.ofNat 64 8 from rfl, h₂]; rfl))
      · exact .inr hDD
    have hrest := (hD' D).resolve_right (fun h => h rfl)
    have hK' : ∀ d' m', MemRel L d' m' ((D.storeBytes addr (bs.take 8)).storeBytes (addr + 8) (bs.drop 8)) →
        K d' m' := fun d' m' h => hK d' m' (by rw [hsplit]; exact h)
    have hok' := ok_piece_succ hok
    dsimp only [storePiecesMem]
    cases hd : d.loadBytes addr 8 with
    | some _ =>
      dsimp only
      have hrel' := hrel.storeBytes_priv (bs := bs.take 8) (by rw [hlen8, hd]; rfl)
      exact ih (addr + 8) (bs.drop 8) _ _ m K hrel' hok' hrest hlen' (by omega) hK'
    | none =>
      dsimp only
      split
      · trivial
      · rcases ok_piece_zero hok with hmem | hoff
        · have hrel' := hrel.store_shared hL hmem (w := 64) rfl (pieceVal (bs.take 8)) tid
          rw [Mem.storeInt, show Int.toBytes 8 (pieceVal (bs.take 8)).toInt = bs.take 8 from
            toBytes_ofInt_ofBytes rfl hlen8] at hrel'
          exact ih (addr + 8) (bs.drop 8) _ _ _ K hrel' hok' hrest hlen' (by omega) hK'
        · rw [hrel.loadBytes_off hoff, hd] at h₁
          cases h₁

private theorem atomic_w128 {atomic : Bool} {w : AvxWidth} (h : (atomic && w == .W128) = true) : w = .W128 := by
  cases atomic <;> cases w <;> first | rfl | exact absurd h (by decide)

theorem loadAvx_sim {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {w : AvxWidth} {k : w.type → MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.loadAvx ⟨r, z, f, D⟩ addr w k checkAlign atomic).AllW L P) :
    (MachineData.loadAvx ⟨r, z, f, d⟩ addr w k checkAlign atomic).AllMem tid m Q := by
  unfold MachineData.loadAvx at h ⊢
  split
  · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact h.elim
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllW, Effects.AllMem] at h ⊢
    obtain ⟨hok, h⟩ := h
    cases hd : Mem.loadInt d addr w.bytes with
    | some x =>
      rw [hrel.loadInt_priv hd] at h
      exact hk _ _ _ _ _ _ _ hrel h
    | none =>
      simp only [Effects.AllMem]
      unfold SharedLayout.AvxOk at hok
      split
      · rename_i hat
        rw [ite_eq_left_of_eq_true _ _ (eq_true hat)] at hok
        obtain rfl := atomic_w128 hat
        rcases hrel.loadInt_none hd hok with ⟨_, hD⟩ | hD
        · rw [hD] at h
          simp only at h
          rw [sharedBytes_val m addr (w := AvxWidth.W128.bits) (n := 16) rfl, sharedLoc_eq] at h
          exact hk _ _ _ _ _ _ _ hrel h
        · rw [hD] at h; exact h.elim
      · rename_i hat
        rw [ite_eq_right_of_eq_false _ _ (eq_false hat)] at hok
        cases hD : Mem.loadInt D addr w.bytes with
        | none => rw [hD] at h; exact h.elim
        | some x =>
          rw [hD] at h
          simp only at h
          unfold Mem.loadInt at hD
          cases hb : D.loadBytes addr w.bytes with
          | none => rw [hb] at hD; cases hD
          | some bs =>
            rw [hb] at hD
            obtain rfl : Int.ofBytes bs = x := Option.some.inj hD
            rw [avx_bytes_eq w] at hb
            exact loadPiecesMem_of hrel _ addr bs _ hok hb (hk _ _ _ _ _ _ _ hrel h)

theorem storeAvx_sim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {w : AvxWidth} {v : w.type} {k : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.storeAvx ⟨r, z, f, D⟩ addr v k checkAlign atomic).AllW L P) :
    (MachineData.storeAvx ⟨r, z, f, d⟩ addr v k checkAlign atomic).AllMem tid m Q := by
  unfold MachineData.storeAvx at h ⊢
  split
  · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact h.elim
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllW, Effects.AllMem] at h ⊢
    obtain ⟨hok, h⟩ := h
    cases hd : Mem.loadInt d addr w.bytes with
    | some x =>
      rw [hrel.loadInt_priv hd] at h
      exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      simp only [Effects.AllMem]
      unfold SharedLayout.AvxOk at hok
      split
      · rename_i hat
        rw [ite_eq_left_of_eq_true _ _ (eq_true hat)] at hok
        obtain rfl := atomic_w128 hat
        rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
        · rw [hD] at h
          exact hk _ _ _ _ _ _ (hrel.store_shared hL hmem (w := 128) rfl v tid) h
        · rw [hD] at h; exact h.elim
      · rename_i hat
        rw [ite_eq_right_of_eq_false _ _ (eq_false hat)] at hok
        cases hD : Mem.loadInt D addr w.bytes with
        | none => rw [hD] at h; exact h.elim
        | some x =>
          rw [hD] at h
          simp only at h
          have hb : (D.loadBytes addr (8 * (w.bytes / 8))).isSome := by
            rw [← avx_bytes_eq w]; exact Mem.loadBytes_isSome_of_loadInt hD
          exact storePiecesMem_of hL _ addr _ d D m _ hrel hok hb
            (by rw [Int.toBytes_length]; exact avx_bytes_eq w) (by cases w <;> decide) fun d' m' hrel' => hk _ _ _ _ _ _ hrel' h

theorem rmw16K_sim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {rk : Kraken.RmwKind} {addr : BitVec 64} {op : BitVec 128 → Option (BitVec 128)}
    {k : BitVec 128 → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.rmw16K ⟨r, z, f, D⟩ rk addr op k).AllW L P) :
    (MachineData.rmw16K ⟨r, z, f, d⟩ rk addr op k).AllMem tid m Q := by
  unfold MachineData.rmw16K at h ⊢
  simp only [Effects.AllW, Effects.AllMem] at h ⊢
  obtain ⟨hok, -, h⟩ := h
  have hok : L.Ok addr 16 := by
    unfold SharedLayout.AvxOk at hok
    rwa [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hok
  cases hd : Mem.loadInt d addr 16 with
  | some x =>
    rw [hrel.loadInt_priv hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt 128 x) with
    | some v =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    simp only [Effects.AllMem]
    rcases hrel.loadInt_none hd hok with ⟨hmem, hD⟩ | hD
    · rw [hD] at h
      simp only at h
      rw [sharedBytes_val m addr (w := 128) (n := 16) rfl, sharedLoc_eq, BitVec.setWidth_eq] at h
      cases hop : op (m.finalVal (loc addr 16)) with
      | some v =>
        rw [hop] at h
        have hrel' := hrel.store_shared hL hmem (w := 128) rfl v tid
        rw [BitVec.setWidth_eq] at hrel'
        exact hk _ _ _ _ _ _ _ hrel' h
      | none =>
        rw [hop] at h
        exact hk _ _ _ _ _ _ _ hrel h
    · rw [hD] at h
      exact h.elim

theorem rmw16Plain_sim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {addr : BitVec 64} {op : BitVec 128 → Option (BitVec 128)} {k : BitVec 128 → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.rmw16Plain ⟨r, z, f, D⟩ addr op k).AllW L P) :
    (MachineData.rmw16Plain ⟨r, z, f, d⟩ addr op k).AllMem tid m Q := by
  unfold MachineData.rmw16Plain at h ⊢
  refine loadAvx_sim (fun v r z f D d m hrel h => ?_) hrel h
  cases hop : op v with
  | some new =>
    rw [hop] at h
    exact storeAvx_sim hL (fun r z f D d m hrel h => hk _ _ _ _ _ _ _ hrel h) hrel h
  | none =>
    rw [hop] at h
    exact hk _ _ _ _ _ _ _ hrel h

theorem avxRegOrMem_sim [Labels] [AddressSize] {w : AvxWidth} {o : AvxRegOrMem w} {p : Std.Rco Int64}
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    {checkAlign atomic : Bool}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (o.interp ⟨r, z, f, D⟩ p k checkAlign atomic).AllW L P) :
    (o.interp ⟨r, z, f, d⟩ p k checkAlign atomic).AllMem tid m Q := by
  cases o with
  | avx x => exact hk _ _ _ _ _ _ _ hrel h
  | mem a => exact loadAvx_sim hk hrel h

theorem avxOperand_sim [Labels] [AddressSize] {w : AvxWidth} {o : AvxOperand w} {p : Std.Rco Int64}
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    {checkAlign : Bool}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (o.interp ⟨r, z, f, D⟩ p k checkAlign).AllW L P) :
    (o.interp ⟨r, z, f, d⟩ p k checkAlign).AllMem tid m Q := by
  cases o with
  | regOrMem rm => exact avxRegOrMem_sim hk hrel h

theorem setAvx_sim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {k : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.setAvx ⟨r, z, f, D⟩ dst v p k checkAlign atomic).AllW L P) :
    (MachineData.setAvx ⟨r, z, f, d⟩ dst v p k checkAlign atomic).AllMem tid m Q := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvx, MachineData.setAvxReg] at h ⊢
    exact hk _ _ _ _ _ _ hrel h
  | mem a => exact storeAvx_sim hL hk hrel h

theorem setAvxLegacy_sim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {k : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.setAvxLegacy ⟨r, z, f, D⟩ dst v p k checkAlign atomic).AllW L P) :
    (MachineData.setAvxLegacy ⟨r, z, f, d⟩ dst v p k checkAlign atomic).AllMem tid m Q := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvxLegacy, MachineData.setAvxLegacyReg] at h ⊢
    exact hk _ _ _ _ _ _ hrel h
  | mem a => exact storeAvx_sim hL hk hrel h

theorem regOrMem_sim [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {p : Std.Rco Int64} {r : Reg64s}
    {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (o.interp ⟨r, z, f, D⟩ p k).AllW L P) :
    (o.interp ⟨r, z, f, d⟩ p k).AllMem tid m Q := by
  cases o with
  | reg x => exact hk _ _ _ _ _ _ _ hrel h
  | mem a => exact load_sim hk hrel h

theorem operand_sim [Labels] [AddressSize] {w : Width} {o : Operand w} {p : Std.Rco Int64} {r : Reg64s}
    {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (o.interp ⟨r, z, f, D⟩ p k).AllW L P) :
    (o.interp ⟨r, z, f, d⟩ p k).AllMem tid m Q := by
  cases o with
  | regOrMem rm => exact regOrMem_sim hk hrel h
  | imm v => exact hk _ _ _ _ _ _ _ hrel h

theorem relRegOrMem_sim [Labels] [AddressSize] {o : RelRegOrMem} {p : Std.Rco Int64} {r : Reg64s}
    {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : BitVec 64 → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (o.interp ⟨r, z, f, D⟩ p k).AllW L P) :
    (o.interp ⟨r, z, f, d⟩ p k).AllMem tid m Q := by
  cases o with
  | rel c => exact hk _ _ _ _ _ _ _ hrel h
  | reg x => exact hk _ _ _ _ _ _ _ hrel h
  | mem a => exact load_sim hk hrel h

theorem set_sim (hL : L.WF) [Labels] [AddressSize] {w : Width} {dst : Dst w} {v : w.type} {p : Std.Rco Int64}
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : MachineData → Effects}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (MachineData.set ⟨r, z, f, D⟩ dst v p k).AllW L P) :
    (MachineData.set ⟨r, z, f, d⟩ dst v p k).AllMem tid m Q := by
  cases dst with
  | reg x =>
    simp only [MachineData.set, MachineData.setReg] at h ⊢
    exact hk _ _ _ _ _ _ hrel h
  | mem a => exact store_sim hL hk hrel h

theorem rmw_sim (hL : L.WF) [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {lock : Bool}
    {p : Std.Rco Int64} {op : w.type → Option w.type} {r : Reg64s} {z : RegZmms} {f : StatusFlags}
    {D d : DataMem} {m : Memory} {k : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d m, MemRel L d m D → (k v ⟨r, z, f, D⟩).AllW L P → (k v ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (o.rmw lock ⟨r, z, f, D⟩ p op k).AllW L P) :
    (o.rmw lock ⟨r, z, f, d⟩ p op k).AllMem tid m Q := by
  cases o with
  | reg x =>
    unfold RegOrMem.rmw at h ⊢
    simp only [MachineData.setReg] at h ⊢
    cases hop : op (r.get x) <;> simp only [hop] at h ⊢ <;> exact hk _ _ _ _ _ _ _ hrel h
  | mem a =>
    unfold RegOrMem.rmw at h ⊢
    cases lock with
    | true => exact rmwK_sim hL hk hrel h
    | false => exact rmwPlain_sim hL hk hrel h

/-- A shift count reads the registers only. -/
theorem _root_.ShiftCountExpr.interp_mk [Labels] (c : ShiftCountExpr) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) (D : DataMem) (p : Std.Rco Int64) :
    c.interp ⟨r, z, f, D⟩ p = c.interp { regs := r } p := by
  cases c <;> rfl

/-! ## The simulation, per instruction -/

/- The dictionary lemmas are applied by search, as in `Kraken.InterpSound`:
sealing the primitives they are keyed on keeps a failed attempt a comparison of
head symbols. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp MachineData.set
  MachineData.load MachineData.store MachineData.storeNT MachineData.rmwK MachineData.rmwPlain RegOrMem.rmw
  AvxRegOrMem.interp AvxOperand.interp MachineData.setAvx MachineData.setAvxLegacy
  MachineData.loadAvx MachineData.storeAvx MachineData.rmw16K MachineData.rmw16Plain

set_option hygiene false in
/-- Reduce the interpreter on both sides and apply the dictionary until the
continuation hypotheses `hk`/`hj` close every leaf. -/
local macro "sim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Reg.interp, MachineData.setReg, ShiftCountExpr.interpMasked,
      ShiftCountExpr.interp_mk, Effects.AllW, Effects.AllMem] at h ⊢ <;>
    repeat' first
      | exact hk _ _ _ _ _ _ hrel h
      | exact hj _ _ _ _ _ _ _ hrel h
      | exact h.elim
      | refine operand_sim (fun v r z f D d m hrel h => ?_) hrel h
      | refine regOrMem_sim (fun v r z f D d m hrel h => ?_) hrel h
      | refine relRegOrMem_sim (fun v r z f D d m hrel h => ?_) hrel h
      | refine set_sim hL (fun r z f D d m hrel h => ?_) hrel h
      | refine load_sim (fun v r z f D d m hrel h => ?_) hrel h
      | refine store_sim hL (fun r z f D d m hrel h => ?_) hrel h
      | refine storeNT_sim hL (fun r z f D d m hrel h => ?_) hrel h
      | refine rmwK_sim hL (fun v r z f D d m hrel h => ?_) hrel h
      | refine rmw_sim hL (fun v r z f D d m hrel h => ?_) hrel h
      | (refine fun v => ?_; specialize h v)
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [Reg.interp, MachineData.setReg, ShiftCountExpr.interpMasked, ShiftCountExpr.interp_mk,
          Effects.AllW, Effects.AllMem] at h ⊢))

-- Each of the 51 cases fits the default budget; together they do not.
set_option maxHeartbeats 1000000 in
theorem operation_sim (hL : L.WF) [Labels] [AddressSize] {w : Width} (op : Operation w) (p : Std.Rco Int64)
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : MachineData → Effects}
    {j : Int64 → MachineData → Effects}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hj : ∀ pc r z f D d m, MemRel L d m D → (j pc ⟨r, z, f, D⟩).AllW L P → (j pc ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (Operation.interp op p ⟨r, z, f, D⟩ k j).AllW L P) :
    (Operation.interp op p ⟨r, z, f, d⟩ k j).AllMem tid m Q := by
  cases op
  -- `xadd` branches on the destination's shape, `bswap` on the width.
  case xadd lock dst src => cases dst <;> sim_search
  case bswap dst => cases w <;> sim_search
  all_goals sim_search

set_option hygiene false in
/-- `sim_search` for the vector operations. -/
local macro "avx_sim_search" : tactic =>
  `(tactic| (
    simp only [AvxOperation.interp, MachineData.setAvxReg, Effects.AllW, Effects.AllMem] at h ⊢ <;>
    repeat' first
      | exact hk _ _ _ _ _ _ hrel h
      | exact h.elim
      | refine avxOperand_sim (fun v r z f D d m hrel h => ?_) hrel h
      | refine avxRegOrMem_sim (fun v r z f D d m hrel h => ?_) hrel h
      | refine setAvx_sim hL (fun r z f D d m hrel h => ?_) hrel h
      | refine setAvxLegacy_sim hL (fun r z f D d m hrel h => ?_) hrel h
      | refine rmw16K_sim hL (fun v r z f D d m hrel h => ?_) hrel h
      | refine rmw16Plain_sim hL (fun v r z f D d m hrel h => ?_) hrel h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setAvxReg, Effects.AllW, Effects.AllMem] at h ⊢))

theorem avxOperation_sim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w)
    (p : Std.Rco Int64) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
    {k : MachineData → Effects}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (AvxOperation.interp op p ⟨r, z, f, D⟩ k).AllW L P) :
    (AvxOperation.interp op p ⟨r, z, f, d⟩ k).AllMem tid m Q := by
  cases op <;> avx_sim_search

theorem instr_sim (hL : L.WF) [Labels] (i : Instr) (p : Std.Rco Int64)
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : MachineData → Effects}
    {j : Int64 → MachineData → Effects}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hj : ∀ pc r z f D d m, MemRel L d m D → (j pc ⟨r, z, f, D⟩).AllW L P → (j pc ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (i.interp ⟨r, z, f, D⟩ p k j).AllW L P) :
    (i.interp ⟨r, z, f, d⟩ p k j).AllMem tid m Q := by
  cases i with
  | regular asz osz op =>
    simp only [Instr.interp, Effects.AllW, Effects.AllMem] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact operation_sim hL op p hk hj hrel h
  | avx asz osz aop =>
    simp only [Instr.interp, Effects.AllW, Effects.AllMem] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact avxOperation_sim hL aop p hk hrel h

theorem directive_sim (hL : L.WF) [Labels] (dir : Directive) (p : Std.Rco Int64)
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory} {k : MachineData → Effects}
    {j : Int64 → MachineData → Effects}
    (hk : ∀ r z f D d m, MemRel L d m D → (k ⟨r, z, f, D⟩).AllW L P → (k ⟨r, z, f, d⟩).AllMem tid m Q)
    (hj : ∀ pc r z f D d m, MemRel L d m D → (j pc ⟨r, z, f, D⟩).AllW L P → (j pc ⟨r, z, f, d⟩).AllMem tid m Q)
    (hrel : MemRel L d m D) (h : (dir.interp ⟨r, z, f, D⟩ p k j).AllW L P) :
    (dir.interp ⟨r, z, f, d⟩ p k j).AllMem tid m Q := by
  cases dir with
  | instr i => exact instr_sim hL i p hk hj hrel h
  | label l => exact hk _ _ _ _ _ _ hrel h
  | byteArray b => exact h.elim

theorem directives_sim (hL : L.WF) [Labels] (ds : List (Directive × Nat)) :
    ∀ (pc : Int64) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {m : Memory}
      {ret : Int64 → MachineData → Effects},
      (∀ pc r z f D d m, MemRel L d m D → (ret pc ⟨r, z, f, D⟩).AllW L P →
        (ret pc ⟨r, z, f, d⟩).AllMem tid m Q) →
      MemRel L d m D → (Directives.interp ds ⟨r, z, f, D⟩ pc ret).AllW L P →
        (Directives.interp ds ⟨r, z, f, d⟩ pc ret).AllMem tid m Q := by
  induction ds with
  | nil => intro pc r z f D d m ret hret hrel h; exact hret _ _ _ _ _ _ _ hrel h
  | cons x ds ih =>
    intro pc r z f D d m ret hret hrel h
    obtain ⟨dir, sz⟩ := x
    simp only [Directives.interp] at h ⊢
    exact directive_sim hL dir _ (fun r z f D d m hrel h => ih _ hret hrel h) hret hrel h

/-- One instruction, merged under `AllW`, split under `AllMem`: the split run
ends related to a merged state the merged run allows. -/
theorem step_sim (hL : L.WF) {e : _root_.Executable} {r : Reg64s} {z : RegZmms}
    {f : StatusFlags} {D d : DataMem} {m : Memory} {pc : Int64}
    (hQ : ∀ r z f D d m pc, MemRel L d m D → P (⟨r, z, f, D⟩, pc) → Q (⟨r, z, f, d⟩, pc) m)
    (hrel : MemRel L d m D) (h : (Executable.step e (⟨r, z, f, D⟩, pc) .done).AllW L P) :
    (Executable.step e (⟨r, z, f, d⟩, pc) .done).AllMem tid m Q := by
  unfold Executable.step at h ⊢
  letI := Executable.labels e
  exact directives_sim hL _ _
    (fun pc r z f D d m hrel h => hQ r z f D d m pc hrel h) hrel h

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
the thread runs `e` and halts at `endPc`, registers, vector registers, flags
and pc agree, `y`'s memory is the merge of `x`'s private memory and `m`, and
the thread has no declarations (every access is its own footprint, so the
shared locations are `sharedLoc`s). -/
def MergedRel (L : SharedLayout) (e : _root_.Executable) (endPc : Int64) (x : State × Memory) (y : MachineState) :
    Prop :=
  x.1.exe = e ∧ x.1.endPc = endPc ∧ x.1.st.1.regs = y.1.regs ∧ x.1.st.1.zmms = y.1.zmms ∧
    x.1.st.1.status = y.1.status ∧ x.1.st.2 = y.2 ∧ MemRel L x.1.st.1.dmem x.2 y.1.dmem ∧ x.1.decls = {}

/-- The merged judgment simulates the sequential runs of the thread. -/
theorem seqSim_merged {L : SharedLayout} (hL : L.WF) {e : _root_.Executable} (endPc : Int64)
    (tid : Nat) : SeqSim isa tid (MergedRel L e endPc) (step1W L e) := by
  intro x y R hxy hT tree hex
  obtain ⟨⟨exe, endPc', ⟨⟨r, z, f, d⟩, pc⟩, showPc, decls⟩, m⟩ := x
  obtain ⟨⟨r', z', f', D⟩, pc'⟩ := y
  obtain ⟨he, hend, hr, hz, hf, hpc, hrel, hds⟩ := hxy
  simp only at he hend hr hz hf hpc hrel hds
  subst he hend hr hz hf hpc hds
  simp only [isa, exec] at hex
  split at hex
  · cases hex
  · cases hex
    refine (EvTree.allSeq_map tid _ _ m _).mpr ?_
    exact Effects.allMem_sound _ m
      (step_sim hL (fun r z f D d m pc hrel hP =>
        ⟨(⟨r, z, f, D⟩, pc), ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrel, rfl⟩, hP⟩) hrel hT)

/-- Conservativity for Kraken's judgment on x64. A judgment
`Eventually (step1W L e) P` about the merged state `(⟨r, z, f, D⟩, pc)`
carries over to every promise-free run of the one-thread machine whose thread
runs `e` from `(⟨r, z, f, d⟩, pc)` on a memory
`mem` without messages, `D` being the merge of `d` and `mem`: the run met `P`
on the way (at a state whose merge satisfies it), or the judgment still holds
of the merge of where it is. -/
theorem merged_link {L : SharedLayout} (hL : L.WF) (A : Arch) (fuel : Nat) {e : _root_.Executable}
    {endPc : Int64} {showPc : Int64 → String} {r : Reg64s} {z : RegZmms} {f : StatusFlags}
    {d D : DataMem} {pc : Int64} {mem : Memory} (hm : mem.msgs = #[]) (hrel : MemRel L d mem D)
    {P : MachineState → Prop} (hev : Eventually (step1W L e) P (⟨r, z, f, D⟩, pc)) {c : Config isa}
    (hc : ReachablePF A fuel ⟨#[Thread.init ({ exe := e, endPc, st := (⟨r, z, f, d⟩, pc), showPc } : State)], mem⟩
      c) :
    ∃ t', c.threads = #[t'] ∧
      ((∃ x y', SeqReach 0 (({ exe := e, endPc, st := (⟨r, z, f, d⟩, pc), showPc } : State), mem) x ∧
          SeqReach 0 x (t'.st, c.mem) ∧ MergedRel L e endPc x y' ∧ P y') ∨
        ∃ y', MergedRel L e endPc (t'.st, c.mem) y' ∧ Eventually (step1W L e) P y') :=
  reachablePF_sim A fuel (seqSim_merged hL endPc 0) hm (y := (⟨r, z, f, D⟩, pc))
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrel, rfl⟩ hev hc

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
    ∃ D', MemRel L x.1.st.1.dmem x.2 D' ∧
      P (⟨x.1.st.1.regs, x.1.st.1.zmms, x.1.st.1.status, D'⟩, x.1.st.2) := by
  obtain ⟨⟨r, z, f, D⟩, pc⟩ := y
  obtain ⟨-, -, hr, hz, hf, hpc, hrel, -⟩ := h
  refine ⟨D, hrel, ?_⟩
  simp only at hr hz hf hpc
  rw [hr, hz, hf, hpc]
  exact hP

/-- Halting runs: when `P` holds only at `endPc` and a step there changes
nothing (`hstop`: nothing is laid out at `endPc`, or what is there faults), a
promise-free run whose thread has reached `endPc` ends in a state whose merge
satisfies `P`. -/
theorem merged_link_halt {L : SharedLayout} (hL : L.WF) (A : Arch) (fuel : Nat) {e : _root_.Executable}
    {endPc : Int64} {showPc : Int64 → String} {r : Reg64s} {z : RegZmms} {f : StatusFlags}
    {d D : DataMem} {pc : Int64} {mem : Memory} (hm : mem.msgs = #[]) (hrel : MemRel L d mem D)
    {P : MachineState → Prop} (hP : ∀ y, P y → y.2 = endPc) (hstop : ∀ y R, y.2 = endPc → step1W L e y R → R y)
    (hev : Eventually (step1W L e) P (⟨r, z, f, D⟩, pc)) {c : Config isa}
    (hc : ReachablePF A fuel ⟨#[Thread.init ({ exe := e, endPc, st := (⟨r, z, f, d⟩, pc), showPc } : State)], mem⟩
      c)
    {t' : Thread isa} (ht : c.threads = #[t']) (hend : t'.st.st.2 = endPc) :
    ∃ D', MemRel L t'.st.st.1.dmem c.mem D' ∧
      P (⟨t'.st.st.1.regs, t'.st.st.1.zmms, t'.st.st.1.status, D'⟩, endPc) := by
  obtain ⟨t'', ht'', hcase⟩ := merged_link hL A fuel hm hrel hev hc
  rw [ht] at ht''
  have htt : t' = t'' := by simpa using ht''
  subst htt
  rw [← hend]
  rcases hcase with ⟨⟨z₁, z₂⟩, y', -, hz, hzy, hPy⟩ | ⟨y', hy, hev'⟩
  · -- `P` was met at `z`, which is at `endPc`, so the thread halted there
    have hpcz : z₁.st.2 = endPc := hzy.2.2.2.2.2.1.trans (hP y' hPy)
    have hez : z₁.endPc = endPc := hzy.2.1
    have hhalt : isa.exec z₁ = none := by
      simp [isa, exec, hpcz, hez]
    obtain ⟨h1, h2⟩ := Prod.mk.inj (SeqReach.halted hhalt hz)
    subst h1 h2
    exact hzy.post hPy
  · have hpy : y'.2 = endPc := hy.2.2.2.2.2.1.symm.trans hend
    exact hy.post (eventually_stutter hev' fun R hR => hstop y' R hpy hR)

end Kraken.Promising.X64
