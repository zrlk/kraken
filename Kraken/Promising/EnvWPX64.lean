/-
The environment-aware wp and the Promising machine, x64: the statements of
the link statements, as `Prop` definitions, and their proofs
(`memRel_iff_mergeRel`, `lastWrite_to_merged`, `env_link_halt`). Design note:
`Kraken/Promising/EnvWP.md`.

The one-thread instance of `Kraken.EnvWP` is `SharedEnv.lastWrite L`: the
environment state is the value of each shared location, which is what the
merged memory of `Kraken.Promising.MergedMem` holds on the footprint. So a
judgment about the *split* state (shared locations out of `dmem`, as the
Promising machine's thread has them) in the `lastWrite` environment is a
judgment about the *merged* state in the `step1W` logic (`LastWriteToMerged`),
and `merged_link_halt` takes it the rest of the way (`EnvLinkHalt`).

Everything here mentions the Promising memory only through `envRel`, so
a change of `Val`/`Loc` touches `envRel` and nothing else.
-/
import Kraken.EnvWP
import Kraken.Promising.EnvMerge
import Kraken.Promising.SeqLinkX64Step

open Kraken

namespace Kraken.Promising.X64

/-! ## Relating the environment state to the merged memory

`envRel`, `MergeRel`, `gmem` and their lemmas are ISA-free and live in
`Kraken.Promising.EnvMerge` (namespace `Kraken.Promising`); they are
re-exported here under their former `Kraken.Promising.X64` names. -/

export Kraken.Promising (envRel MergeRel gmem gmem_finalVal mergeRel_iff sharedBytes_gmem)

/-- The split state `x` (machine state and `lastWrite` environment state) is
the merged state `y`. -/
def Merged (L : SharedLayout) (x : MachineState × (SharedEnv.lastWrite L).State) (y : MachineState) :
    Prop :=
  x.1.1.regs = y.1.regs ∧ x.1.1.zmms = y.1.zmms ∧ x.1.1.status = y.1.status ∧ x.1.2 = y.2 ∧
    MergeRel L x.1.1.dmem x.2 y.1.dmem

/-! ## Link statements -/

/-- `MemRel` is `MergeRel` at any environment state related to the memory. -/
def MemRelIffMergeRel : Prop :=
  ∀ (L : SharedLayout) (d D : Mem 64) (mem : Memory) (g : BitVec 64 → BitVec 128),
    L.WF → envRel L g mem → (MemRel L d mem D ↔ MergeRel L d g D)

/-- **Shape (ii) recovers shape (i).** A judgment in the `lastWrite`
environment about a split state is a merged judgment (`step1W`, the access
discipline included) about its merge. -/
def LastWriteToMerged : Prop :=
  ∀ [_root_.Layout] (L : SharedLayout) (e : Kraken.Executable Directive) [Kraken.Executable.ValidLayout e],
    L.WF →
    ∀ (P : MachineState × (SharedEnv.lastWrite L).State → Prop)
      (x : MachineState × (SharedEnv.lastWrite L).State) (y : MachineState),
      Merged L x y → Eventually (e.instrStepEnv (SharedEnv.lastWrite L)) P x →
        Eventually (step1W L e) (fun y' => ∃ x', Merged L x' y' ∧ P x') y

/-- **The one-thread link through the environment.** A judgment in the
`lastWrite` environment about the thread's own (split) start state, with the
environment state holding the memory's initial values, holds at the end of
every promise-free one-thread run that halts, with an environment state
holding the memory's final values. `LastWriteToMerged`, then
`merged_link_halt`. -/
def EnvLinkHalt : Prop :=
  ∀ [_root_.Layout] (L : SharedLayout) (e : Kraken.Executable Directive) [Kraken.Executable.ValidLayout e],
    L.WF →
    ∀ (A : Arch) (fuel : Nat) (endPc : Int64) (showPc : Int64 → String) (s : MachineData) (pc : Int64)
      (mem : Memory) (g : BitVec 64 → BitVec 128)
      (P : MachineState × (SharedEnv.lastWrite L).State → Prop),
      mem.msgs = #[] → (∀ k, L.Covers k → s.dmem.get? k = none) → envRel L g mem →
      (∀ x, P x → x.1.2 = endPc) →
      (∀ y R, y.2 = endPc → step1W L e y R → R y) →
      Eventually (e.instrStepEnv (SharedEnv.lastWrite L)) P ((s, pc), g) →
      ∀ c : Config isa, ReachablePF A fuel ⟨#[Thread.init ({ exe := e, endPc, st := (s, pc), showPc } : State)], mem⟩ c →
        ∀ t' : Thread isa, c.threads = #[t'] → t'.st.st.2 = endPc →
          ∃ g', envRel L g' c.mem ∧ P ((t'.st.st.1, endPc), g')

/-! ### `lastWrite` -/

section LastWrite

variable {L : SharedLayout}

/-- The 8-byte pieces from `addr` are shared locations. -/
def PiecesIn (L : SharedLayout) : BitVec 64 → Nat → Prop
  | _, 0 => True
  | addr, n + 1 => (addr, 8) ∈ L ∧ PiecesIn L (addr + 8) n

/-- The environment state's values at the 8-byte pieces from `addr`. -/
def pieceVals (g : BitVec 64 → BitVec 128) : BitVec 64 → Nat → List (BitVec 128)
  | _, 0 => []
  | addr, n + 1 => g addr :: pieceVals g (addr + 8) n

/-- The environment state after the 8-byte pieces `ps` are stored from `addr`. -/
def updPieces (g : BitVec 64 → BitVec 128) : BitVec 64 → List (BitVec 64) → BitVec 64 → BitVec 128
  | _, [] => g
  | addr, p :: ps => updPieces (SharedEnv.upd g addr (p.setWidth 128)) (addr + 8) ps

theorem loadPieces_lastWrite {addr : BitVec 64} {n : Nat} {g : BitVec 64 → BitVec 128}
    {k : List (BitVec 64) → (BitVec 64 → BitVec 128) → Prop}
    (h : (SharedEnv.lastWrite L).LoadPieces addr n g k) :
    PiecesIn L addr n ∧ k ((pieceVals g addr n).map (·.setWidth 64)) g := by
  induction n generalizing addr k with
  | zero => exact ⟨trivial, h⟩
  | succ n ih =>
    obtain ⟨hok, h⟩ := h
    obtain ⟨h1, h2⟩ := ih (h (g addr) g ⟨rfl, rfl⟩)
    exact ⟨⟨hok, h1⟩, h2⟩

theorem storePieces_lastWrite {addr : BitVec 64} {ps : List (BitVec 64)} {g : BitVec 64 → BitVec 128}
    {k : (BitVec 64 → BitVec 128) → Prop}
    (h : (SharedEnv.lastWrite L).StorePieces addr ps g k) :
    PiecesIn L addr ps.length ∧ k (updPieces g addr ps) := by
  induction ps generalizing addr g with
  | nil => exact ⟨trivial, h⟩
  | cons p ps ih =>
    obtain ⟨hok, h⟩ := h
    obtain ⟨h1, h2⟩ := ih (h true _ (.inl ⟨rfl, rfl⟩))
    exact ⟨⟨hok, h1⟩, h2⟩

theorem PiecesIn.mem {addr : BitVec 64} {n : Nat} (h : PiecesIn L addr n) :
    ∀ i < n, (addr + BitVec.ofNat 64 (8 * i), 8) ∈ L := by
  induction n generalizing addr with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := ih h.2 i (by omega)
      have he : addr + BitVec.ofNat 64 (8 * (i + 1)) = addr + 8 + BitVec.ofNat 64 (8 * i) := by
        rw [BitVec.add_assoc]
        show addr + BitVec.ofNat 64 (8 * (i + 1)) = addr + (BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i))
        rw [← BitVec.ofNat_add, show 8 + 8 * i = 8 * (i + 1) by omega]
      rwa [he]

/-- The bytes of the 8-byte pieces of the environment state, little-endian. -/
def piecesBytes (vs : List (BitVec 128)) : List UInt8 :=
  vs.flatMap fun x => Int.toBytes 8 (x.toNat : Int)

theorem _root_.Kraken.Promising.MemRel.loadBytes_pieces {d D : Mem 64} {g : BitVec 64 → BitVec 128}
    (h : MemRel L d (gmem L g) D) {addr : BitVec 64} {n : Nat} (hp : PiecesIn L addr n) :
    D.loadBytes addr (8 * n) = some (piecesBytes (pieceVals g addr n)) := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, Mem.loadBytes_add, h.shared _ _ hp.1,
      show addr + BitVec.ofNat 64 8 = addr + 8 from rfl, ih hp.2]
    simp only [Option.bind_some, Option.map_some, pieceVals, piecesBytes, List.flatMap_cons, sharedBytes,
      gmem_finalVal hp.1]

theorem ofBytes_piecesBytes :
    ∀ vs : List (BitVec 128), Int.ofBytes (piecesBytes vs) = (piecesNat (vs.map (·.setWidth 64)) : Int)
  | [] => rfl
  | x :: vs => by
    have ih := ofBytes_piecesBytes vs
    show Int.ofBytes (Int.toBytes 8 (x.toNat : Int) ++ piecesBytes vs) =
      (((x.setWidth 64).toNat + 2 ^ 64 * piecesNat (vs.map (·.setWidth 64)) : Nat) : Int)
    rw [Int.ofBytes_append, ih, ofBytes_toBytes, Int.toBytes_length, BitVec.toNat_setWidth]
    simp only [Int.take]
    rw [show ((256 : Int) ^ 8) = 2 ^ (8 * 8) from rfl, Int.natCast_add, Int.natCast_mul,
      Int.natCast_emod, Int.natCast_pow]
    rfl

theorem ofInt_ofBytes_piecesBytes (m : Nat) (vs : List (BitVec 128)) :
    BitVec.ofInt m (Int.ofBytes (piecesBytes vs)) = ofPieces m (vs.map (·.setWidth 64)) := by
  rw [ofBytes_piecesBytes, BitVec.ofInt_natCast]
  rfl

private theorem toBytes_toInt {w n : Nat} (hw : w = 8 * n) (v : BitVec w) :
    Int.toBytes n v.toInt = Int.toBytes n (v.toNat : Int) := by
  rw [← Int.toBytes_emod n v.toInt, ← Int.toBytes_emod n (v.toNat : Int), Int.take, Int.take, ← hw,
    BitVec.toInt_eq_toNat_bmod]
  have h2 : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by norm_cast
  rw [h2, Int.bmod_emod]

/-- The bytes of a value at `j + k` bytes are its low `j` bytes, then the bytes
of the rest. -/
private theorem toBytes_add (k : Nat) :
    ∀ (j N : Nat), Int.toBytes (j + k) (N : Int) = Int.toBytes j (N : Int) ++ Int.toBytes k ((N / 256 ^ j : Nat) : Int)
  | 0, N => by simp [Int.toBytes]
  | j + 1, N => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [Int.toBytes, List.cons_append]
    rw [show (N : Int) / 256 = ((N / 256 : Nat) : Int) by omega,
      toBytes_add k j (N / 256), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ j)]

/-- The bytes of a value at `8 n` bytes are the bytes of its 8-byte pieces. -/
private theorem toBytes_pieces :
    ∀ (n N : Nat), Int.toBytes (8 * n) (N : Int) =
      (List.range n).flatMap fun i => Int.toBytes 8 ((N / 2 ^ (64 * i) : Nat) : Int)
  | 0, N => rfl
  | n + 1, N => by
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, toBytes_add, toBytes_pieces n, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    congr 1
    · simp
    · congr 1
      funext i
      rw [Nat.div_div_eq_div_mul, show (256 : Nat) ^ 8 * 2 ^ (64 * i) = 2 ^ (64 * (i + 1)) by
        rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, ← Nat.pow_add]; congr 1; omega]

private theorem toBytes8_mod (N : Nat) : Int.toBytes 8 ((N % 2 ^ 64 : Nat) : Int) = Int.toBytes 8 (N : Int) := by
  rw [← Int.toBytes_emod 8 (N : Int)]
  congr 1

/-- The bytes of a value of `8 n` bytes are the bytes of its pieces, in address
order (little-endian agreement of a whole store with its pieces). -/
theorem toBytes_toPieces {m n : Nat} (hm : m = 64 * n) (v : BitVec m) :
    Int.toBytes (8 * n) v.toInt = (toPieces v n).flatMap fun p => Int.toBytes 8 p.toInt := by
  rw [toBytes_toInt (by omega) v, toBytes_pieces, toPieces, List.flatMap_map]
  congr 1
  funext i
  rw [toBytes_toInt (w := 64) (n := 8) rfl, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, toBytes8_mod]

theorem length_toPieces {m : Nat} (v : BitVec m) (n : Nat) : (toPieces v n).length = n := by
  simp [toPieces]

private theorem length_flatMap_toBytes :
    ∀ ps : List (BitVec 64), (ps.flatMap fun p => Int.toBytes 8 p.toInt).length = 8 * ps.length
  | [] => rfl
  | p :: ps => by
    rw [List.flatMap_cons, List.length_append, Int.toBytes_length, length_flatMap_toBytes ps,
      List.length_cons]
    omega

/-- Storing the 8-byte pieces `ps` of shared locations: the merged memory takes
them, the environment state takes each in turn. -/
theorem _root_.Kraken.Promising.MemRel.storeBytes_pieces (hL : L.WF) {d : Mem 64} :
    ∀ (ps : List (BitVec 64)) (addr : BitVec 64) (g : BitVec 64 → BitVec 128) (D : Mem 64),
      PiecesIn L addr ps.length → MemRel L d (gmem L g) D → 8 * ps.length ≤ 2 ^ 64 →
        MemRel L d (gmem L (updPieces g addr ps)) (D.storeBytes addr (ps.flatMap fun p => Int.toBytes 8 p.toInt))
  | [], addr, g, D, _, h, _ => by rw [List.flatMap_nil, Mem.storeBytes_nil]; exact h
  | p :: ps, addr, g, D, hp, h, hb => by
    rw [List.flatMap_cons, Mem.storeBytes_append _ _ _ _ (by
      rw [Int.toBytes_length, length_flatMap_toBytes]
      simp only [List.length_cons] at hb
      omega), Int.toBytes_length]
    have h1 := h.store_gmem hL hp.1 (w := 64) rfl p
    exact MemRel.storeBytes_pieces hL ps (addr + 8) _ _ hp.2 h1 (by simp only [List.length_cons] at hb; omega)

end LastWrite

/-! ## The simulation of the split run by the merged run, per primitive

The converse direction of `SeqLinkX64`'s `step_sim`: a split state `⟨r, z, f, d⟩`
in `lastWrite L`'s state `g` whose tree satisfies `AllEnv`, and the merged
state `⟨r, z, f, D⟩` with `MemRel L d (gmem L g) D`; the merged tree satisfies
`AllW`. The two trees may have different continuations (`k₁`, `k₂`), related by
the continuation hypothesis: one lemma both transports a cell's step to the
interpreter with real continuations (as `Directive.interp_sound` does) and
moves it from the split to the merged memory. -/

section ESim

variable {L : SharedLayout} {P₁ : MachineState → (BitVec 64 → BitVec 128) → Prop} {P₂ : MachineState → Prop}

local notation "LW" => SharedEnv.lastWrite L

private theorem bits_eq (w : Width) : w.bits = 8 * w.bytes := by cases w <;> rfl

private theorem avx_bytes_eq (w : AvxWidth) : w.bytes = 8 * (w.bytes / 8) := by cases w <;> rfl

theorem lw_ok_fence (k : FenceKind) (g : BitVec 64 → BitVec 128) : (LW).ok (.fence k) g = True := rfl

theorem lw_step_fence (k : FenceKind) (g g' : BitVec 64 → BitVec 128) (u : Unit) :
    (LW).step (.fence k) g u g' = (g' = g) := rfl

theorem load_esim {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {addr : BitVec 64} {w : Width} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.load ⟨r, z, f, d⟩ addr w k₁).AllEnv LW g P₁) :
    (MachineData.load ⟨r, z, f, D⟩ addr w k₂).AllW L P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    exact hk _ _ _ _ _ _ _ hrel (h _ _ ⟨rfl, rfl⟩)

theorem store_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {addr : BitVec 64} {w : Width} {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.store ⟨r, z, f, d⟩ addr v k₁).AllEnv LW g P₁) :
    (MachineData.store ⟨r, z, f, D⟩ addr v k₂).AllW L P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    exact hk _ _ _ _ _ _ (hrel.store_gmem hL hmem (bits_eq w) v) (h true _ (.inl ⟨rfl, rfl⟩))

/-- `store_esim` for a non-temporal store, whose unmapped access is a `sync_store`. -/
theorem storeNT_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {addr : BitVec 64} {w : Width} {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.storeNT ⟨r, z, f, d⟩ addr v k₁).AllEnv LW g P₁) :
    (MachineData.storeNT ⟨r, z, f, D⟩ addr v k₂).AllW L P₂ := by
  unfold MachineData.storeNT at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    exact hk _ _ _ _ _ _ (hrel.store_gmem hL hmem (bits_eq w) v) (h true _ (.inl ⟨rfl, rfl⟩))

theorem rmwK_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.rmwK ⟨r, z, f, d⟩ rk addr w op k₁).AllEnv LW g P₁) :
    (MachineData.rmwK ⟨r, z, f, D⟩ rk addr w op k₂).AllW L P₂ := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    simp only at h ⊢
    cases hop : op (BitVec.ofInt w.bits x) with
    | some v =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, .inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    cases hop : op ((g addr).setWidth w.bits) with
    | some v =>
      have hop' : rmwOp128 w op (g addr) = some (v.setWidth 128) := by simp [rmwOp128, hop]
      exact hk _ _ _ _ _ _ _ (hrel.store_gmem hL hmem (bits_eq w) v) (h (g addr) _ ⟨rfl, by rw [hop']⟩)
    | none =>
      have hop' : rmwOp128 w op (g addr) = none := by simp [rmwOp128, hop]
      exact hk _ _ _ _ _ _ _ hrel (h (g addr) g ⟨rfl, by rw [hop']⟩)

theorem rmwPlain_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {addr : BitVec 64} {w : Width} {op : w.type → Option w.type}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.rmwPlain ⟨r, z, f, d⟩ addr w op k₁).AllEnv LW g P₁) :
    (MachineData.rmwPlain ⟨r, z, f, D⟩ addr w op k₂).AllW L P₂ := by
  unfold MachineData.rmwPlain at h ⊢
  refine load_esim (fun v r z f D d g hrel h => ?_) hrel h
  cases hop : op v with
  | some new =>
    simp only [hop] at h ⊢
    exact store_esim hL (fun r z f D d g hrel h => hk _ _ _ _ _ _ _ hrel h) hrel h
  | none =>
    simp only [hop] at h ⊢
    exact hk _ _ _ _ _ _ _ hrel h

/-! ### Vector accesses -/

private theorem atomic_w128 {atomic : Bool} {w : AvxWidth} (h : (atomic && w == .W128) = true) : w = .W128 := by
  cases atomic <;> cases w <;> first | rfl | exact absurd h (by decide)

/-- A vector access the private memory serves respects the layout as split. -/
theorem avxOk_of_loadBytes {d D : Mem 64} {m : Memory} (h : MemRel L d m D) {atomic : Bool}
    {addr : BitVec 64} {w : AvxWidth} (hd : (d.loadBytes addr w.bytes).isSome) : L.AvxOk atomic addr w := by
  unfold SharedLayout.AvxOk
  split
  · rename_i hat
    obtain rfl := atomic_w128 hat
    exact .inr (h.ok_of_loadBytes hd)
  · intro i hi
    refine .inr fun j hj => ?_
    have := h.ok_of_loadBytes hd (8 * i + j) (by have := avx_bytes_eq w; omega)
    rwa [BitVec.ofNat_add, ← BitVec.add_assoc] at this

/-- A shared location accessed whole by a vector access is 16 bytes wide. -/
private theorem w128_of_mem (hL : L.WF) {addr : BitVec 64} {w : AvxWidth} (h : (addr, w.bytes) ∈ L) :
    w = .W128 := by
  have := hL.le16 _ _ h
  cases w <;> simp_all

private theorem avxOk_atomic {addr : BitVec 64} (h : (addr, 16) ∈ L) : L.AvxOk true addr .W128 := by
  unfold SharedLayout.AvxOk
  exact .inl h

private theorem avxOk_pieces {addr : BitVec 64} {w : AvxWidth} (h : PiecesIn L addr (w.bytes / 8)) :
    L.AvxOk false addr w := by
  unfold SharedLayout.AvxOk
  exact fun i hi => .inl (h.mem i hi)

theorem loadAvx_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {addr : BitVec 64} {w : AvxWidth} {k₁ k₂ : w.type → MachineData → Effects}
    {checkAlign atomic : Bool}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D)
    (h : (MachineData.loadAvx ⟨r, z, f, d⟩ addr w k₁ checkAlign atomic).AllEnv LW g P₁) :
    (MachineData.loadAvx ⟨r, z, f, D⟩ addr w k₂ checkAlign atomic).AllW L P₂ := by
  unfold MachineData.loadAvx at h ⊢
  split
  · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact h.elim
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllW, Effects.AllEnv] at h ⊢
    cases hd : Mem.loadInt d addr w.bytes with
    | some x =>
      rw [hd] at h
      refine ⟨avxOk_of_loadBytes hrel (Mem.loadBytes_isSome_of_loadInt hd), ?_⟩
      rw [hrel.loadInt_priv hd]
      exact hk _ _ _ _ _ _ _ hrel h
    | none =>
      rw [hd] at h
      cases atomic with
      | true =>
        simp only [Effects.AllEnv] at h
        obtain ⟨hok, h⟩ := h
        have hmem : (addr, w.bytes) ∈ L := hok
        obtain rfl := w128_of_mem hL hmem
        refine ⟨avxOk_atomic hmem, ?_⟩
        rw [hrel.loadInt_gmem hmem]
        simp only
        rw [sharedBytes_gmem (w := AvxWidth.W128.bits) hmem rfl]
        exact hk _ _ _ _ _ _ _ hrel (h _ _ ⟨rfl, rfl⟩)
      | false =>
        simp only [Effects.AllEnv] at h
        obtain ⟨hp, h⟩ := loadPieces_lastWrite h
        refine ⟨avxOk_pieces hp, ?_⟩
        have hb := hrel.loadBytes_pieces hp
        rw [← avx_bytes_eq w] at hb
        have hD : Mem.loadInt D addr w.bytes = some (Int.ofBytes (piecesBytes (pieceVals g addr (w.bytes / 8)))) := by
          unfold Mem.loadInt; rw [hb]; rfl
        rw [hD]
        simp only
        rw [ofInt_ofBytes_piecesBytes]
        exact hk _ _ _ _ _ _ _ hrel h

theorem storeAvx_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {addr : BitVec 64} {w : AvxWidth} {v : w.type} {k₁ k₂ : MachineData → Effects}
    {checkAlign atomic : Bool}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D)
    (h : (MachineData.storeAvx ⟨r, z, f, d⟩ addr v k₁ checkAlign atomic).AllEnv LW g P₁) :
    (MachineData.storeAvx ⟨r, z, f, D⟩ addr v k₂ checkAlign atomic).AllW L P₂ := by
  unfold MachineData.storeAvx at h ⊢
  split
  · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact h.elim
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllW, Effects.AllEnv] at h ⊢
    cases hd : Mem.loadInt d addr w.bytes with
    | some x =>
      rw [hd] at h
      refine ⟨avxOk_of_loadBytes hrel (Mem.loadBytes_isSome_of_loadInt hd), ?_⟩
      rw [hrel.loadInt_priv hd]
      exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hd] at h
      cases atomic with
      | true =>
        simp only [Effects.AllEnv] at h
        obtain ⟨hok, h⟩ := h
        have hmem : (addr, w.bytes) ∈ L := hok
        obtain rfl := w128_of_mem hL hmem
        refine ⟨avxOk_atomic hmem, ?_⟩
        rw [hrel.loadInt_gmem hmem]
        exact hk _ _ _ _ _ _ (hrel.store_gmem hL hmem (w := 128) rfl v) (h true _ (.inl ⟨rfl, rfl⟩))
      | false =>
        simp only [Effects.AllEnv] at h
        obtain ⟨hp, h⟩ := storePieces_lastWrite h
        rw [length_toPieces] at hp
        refine ⟨avxOk_pieces hp, ?_⟩
        have hb := hrel.loadBytes_pieces hp
        rw [← avx_bytes_eq w] at hb
        have hD : Mem.loadInt D addr w.bytes = some (Int.ofBytes (piecesBytes (pieceVals g addr (w.bytes / 8)))) := by
          unfold Mem.loadInt; rw [hb]; rfl
        rw [hD]
        simp only
        have hst : Mem.storeInt D addr w.bytes v.toInt =
            D.storeBytes addr ((toPieces v (w.bytes / 8)).flatMap fun p => Int.toBytes 8 p.toInt) := by
          rw [Mem.storeInt, ← toBytes_toPieces (by cases w <;> rfl) v, ← avx_bytes_eq w]
        rw [hst]
        refine hk _ _ _ _ _ _ (MemRel.storeBytes_pieces hL _ addr g D (by rw [length_toPieces]; exact hp) hrel
          (by rw [length_toPieces]; cases w <;> decide)) h

theorem rmw16K_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {rk : Kraken.RmwKind} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {k₁ k₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.rmw16K ⟨r, z, f, d⟩ rk addr op k₁).AllEnv LW g P₁) :
    (MachineData.rmw16K ⟨r, z, f, D⟩ rk addr op k₂).AllW L P₂ := by
  unfold MachineData.rmw16K at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr 16 with
  | some x =>
    rw [hd] at h
    have hok := avxOk_of_loadBytes (atomic := true) (w := .W128) hrel (Mem.loadBytes_isSome_of_loadInt hd)
    refine ⟨hok, hok, ?_⟩
    rw [hrel.loadInt_priv hd]
    simp only at h ⊢
    cases hop : op (BitVec.ofInt 128 x) with
    | some v =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ _ hrel h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, 16) ∈ L := hok
    refine ⟨avxOk_atomic hmem, avxOk_atomic hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    simp only
    rw [sharedBytes_gmem hmem rfl, BitVec.setWidth_eq]
    cases hop : op (g addr) with
    | some v =>
      have hrel' := hrel.store_gmem hL hmem (w := 128) rfl v
      rw [BitVec.setWidth_eq] at hrel'
      exact hk _ _ _ _ _ _ _ hrel' (h (g addr) _ ⟨rfl, by rw [hop]⟩)
    | none =>
      exact hk _ _ _ _ _ _ _ hrel (h (g addr) g ⟨rfl, by rw [hop]⟩)

theorem rmw16Plain_esim (hL : L.WF) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {addr : BitVec 64} {op : BitVec 128 → Option (BitVec 128)}
    {k₁ k₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.rmw16Plain ⟨r, z, f, d⟩ addr op k₁).AllEnv LW g P₁) :
    (MachineData.rmw16Plain ⟨r, z, f, D⟩ addr op k₂).AllW L P₂ := by
  unfold MachineData.rmw16Plain at h ⊢
  refine loadAvx_esim hL (fun v r z f D d g hrel h => ?_) hrel h
  cases hop : op v with
  | some new =>
    simp only [hop] at h ⊢
    exact storeAvx_esim hL (fun r z f D d g hrel h => hk _ _ _ _ _ _ _ hrel h) hrel h
  | none =>
    simp only [hop] at h ⊢
    exact hk _ _ _ _ _ _ _ hrel h

theorem avxRegOrMem_esim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} {o : AvxRegOrMem w}
    {p : Std.Rco Int64} {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (o.interp ⟨r, z, f, d⟩ p k₁ checkAlign atomic).AllEnv LW g P₁) :
    (o.interp ⟨r, z, f, D⟩ p k₂ checkAlign atomic).AllW L P₂ := by
  cases o with
  | avx x => exact hk _ _ _ _ _ _ _ hrel h
  | mem a => exact loadAvx_esim hL hk hrel h

theorem avxOperand_esim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} {o : AvxOperand w}
    {p : Std.Rco Int64} {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign : Bool}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (o.interp ⟨r, z, f, d⟩ p k₁ checkAlign).AllEnv LW g P₁) :
    (o.interp ⟨r, z, f, D⟩ p k₂ checkAlign).AllW L P₂ := by
  cases o with
  | regOrMem rm => exact avxRegOrMem_esim hL hk hrel h

theorem setAvx_esim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D)
    (h : (MachineData.setAvx ⟨r, z, f, d⟩ dst v p k₁ checkAlign atomic).AllEnv LW g P₁) :
    (MachineData.setAvx ⟨r, z, f, D⟩ dst v p k₂ checkAlign atomic).AllW L P₂ := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvx, MachineData.setAvxReg] at h ⊢
    exact hk _ _ _ _ _ _ hrel h
  | mem a => exact storeAvx_esim hL hk hrel h

theorem setAvxLegacy_esim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D)
    (h : (MachineData.setAvxLegacy ⟨r, z, f, d⟩ dst v p k₁ checkAlign atomic).AllEnv LW g P₁) :
    (MachineData.setAvxLegacy ⟨r, z, f, D⟩ dst v p k₂ checkAlign atomic).AllW L P₂ := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvxLegacy, MachineData.setAvxLegacyReg] at h ⊢
    exact hk _ _ _ _ _ _ hrel h
  | mem a => exact storeAvx_esim hL hk hrel h

theorem regOrMem_esim [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {p : Std.Rco Int64} {r : Reg64s}
    {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (o.interp ⟨r, z, f, d⟩ p k₁).AllEnv LW g P₁) :
    (o.interp ⟨r, z, f, D⟩ p k₂).AllW L P₂ := by
  cases o with
  | reg x => exact hk _ _ _ _ _ _ _ hrel h
  | mem a => exact load_esim hk hrel h

theorem operand_esim [Labels] [AddressSize] {w : Width} {o : Operand w} {p : Std.Rco Int64} {r : Reg64s}
    {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (o.interp ⟨r, z, f, d⟩ p k₁).AllEnv LW g P₁) :
    (o.interp ⟨r, z, f, D⟩ p k₂).AllW L P₂ := by
  cases o with
  | regOrMem rm => exact regOrMem_esim hk hrel h
  | imm v => exact hk _ _ _ _ _ _ _ hrel h

theorem relRegOrMem_esim [Labels] [AddressSize] {o : RelRegOrMem} {p : Std.Rco Int64} {r : Reg64s}
    {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : BitVec 64 → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (o.interp ⟨r, z, f, d⟩ p k₁).AllEnv LW g P₁) :
    (o.interp ⟨r, z, f, D⟩ p k₂).AllW L P₂ := by
  cases o with
  | rel c => exact hk _ _ _ _ _ _ _ hrel h
  | reg x => exact hk _ _ _ _ _ _ _ hrel h
  | mem a => exact load_esim hk hrel h

theorem set_esim (hL : L.WF) [Labels] [AddressSize] {w : Width} {dst : Dst w} {v : w.type} {p : Std.Rco Int64}
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.set ⟨r, z, f, d⟩ dst v p k₁).AllEnv LW g P₁) :
    (MachineData.set ⟨r, z, f, D⟩ dst v p k₂).AllW L P₂ := by
  cases dst with
  | reg x =>
    simp only [MachineData.set, MachineData.setReg] at h ⊢
    exact hk _ _ _ _ _ _ hrel h
  | mem a => exact store_esim hL hk hrel h

theorem rmw_esim (hL : L.WF) [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {lock : Bool}
    {p : Std.Rco Int64} {op : w.type → Option w.type} {r : Reg64s} {z : RegZmms} {f : StatusFlags}
    {D d : DataMem} {g : BitVec 64 → BitVec 128} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r z f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (o.rmw lock ⟨r, z, f, d⟩ p op k₁).AllEnv LW g P₁) :
    (o.rmw lock ⟨r, z, f, D⟩ p op k₂).AllW L P₂ := by
  cases o with
  | reg x =>
    unfold RegOrMem.rmw at h ⊢
    simp only [MachineData.setReg] at h ⊢
    cases hop : op (r.get x) <;> simp only [hop] at h ⊢ <;> exact hk _ _ _ _ _ _ _ hrel h
  | mem a =>
    unfold RegOrMem.rmw at h ⊢
    cases lock with
    | true => exact rmwK_esim hL hk hrel h
    | false => exact rmwPlain_esim hL hk hrel h

/-! ### Per instruction -/

/- As in `SeqLinkX64`: the dictionary lemmas are applied by search, the
primitives they are keyed on sealed. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp MachineData.set
  MachineData.load MachineData.store MachineData.storeNT MachineData.rmwK MachineData.rmwPlain RegOrMem.rmw
  AvxRegOrMem.interp AvxOperand.interp MachineData.setAvx MachineData.setAvxLegacy
  MachineData.loadAvx MachineData.storeAvx MachineData.rmw16K MachineData.rmw16Plain

set_option hygiene false in
/-- Reduce the interpreter on both sides and apply the dictionary until the
continuation hypotheses `hk`/`hj` close every leaf. -/
local macro "esim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Reg.interp, MachineData.setReg, ShiftCountExpr.interpMasked,
      ShiftCountExpr.interp_mk, Effects.AllW, Effects.AllEnv, lw_ok_fence, lw_step_fence, true_and,
      forall_eq'] at h ⊢ <;>
    repeat' first
      | exact hk _ _ _ _ _ _ hrel h
      | exact hj _ _ _ _ _ _ _ hrel h
      | exact hk _ _ _ _ _ _ hrel (h g rfl)
      | exact h.elim
      | refine operand_esim (fun v r z f D d g hrel h => ?_) hrel h
      | refine regOrMem_esim (fun v r z f D d g hrel h => ?_) hrel h
      | refine relRegOrMem_esim (fun v r z f D d g hrel h => ?_) hrel h
      | refine set_esim hL (fun r z f D d g hrel h => ?_) hrel h
      | refine load_esim (fun v r z f D d g hrel h => ?_) hrel h
      | refine store_esim hL (fun r z f D d g hrel h => ?_) hrel h
      | refine storeNT_esim hL (fun r z f D d g hrel h => ?_) hrel h
      | refine rmwK_esim hL (fun v r z f D d g hrel h => ?_) hrel h
      | refine rmw_esim hL (fun v r z f D d g hrel h => ?_) hrel h
      | (refine fun v => ?_; specialize h v)
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [Reg.interp, MachineData.setReg, ShiftCountExpr.interpMasked, ShiftCountExpr.interp_mk,
          Effects.AllW, Effects.AllEnv, lw_ok_fence, lw_step_fence, true_and, forall_eq'] at h ⊢))

set_option maxHeartbeats 1000000 in
theorem operation_esim (hL : L.WF) [Labels] [AddressSize] {w : Width} (op : Operation w) (p : Std.Rco Int64)
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hj : ∀ pc r z f D d g, MemRel L d (gmem L g) D → (j₁ pc ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (j₂ pc ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (Operation.interp op p ⟨r, z, f, d⟩ k₁ j₁).AllEnv LW g P₁) :
    (Operation.interp op p ⟨r, z, f, D⟩ k₂ j₂).AllW L P₂ := by
  cases op
  case xadd lock dst src => cases dst <;> esim_search
  case bswap dst => cases w <;> esim_search
  -- `movfs` is `mov` at a segment-relative address: unfold the segment forms.
  case movfs dst src =>
    rcases src with (_ | a) | v <;> rcases dst with _ | b <;>
      simp only [Operation.interp, Operand.interpSeg, RegOrMem.interpSeg, MachineData.setSeg] at h ⊢ <;>
      repeat' first
        | exact hk _ _ _ _ _ _ hrel h
        | refine load_esim (fun v r z f D d g hrel h => ?_) hrel h
        | refine store_esim hL (fun r z f D d g hrel h => ?_) hrel h
        | simp only [MachineData.setSeg] at h ⊢
  -- `cmpfs` is `cmp` at a segment-relative address: unfold the segment forms.
  case cmpfs x y =>
    rcases y with (_ | b) | v <;> rcases x with _ | a <;>
      simp only [Operation.interp, Operand.interpSeg, RegOrMem.interpSeg, MachineData.setSeg] at h ⊢ <;>
      repeat' first
        | exact hk _ _ _ _ _ _ hrel h
        | refine load_esim (fun v r z f D d g hrel h => ?_) hrel h
        | refine store_esim hL (fun r z f D d g hrel h => ?_) hrel h
        | simp only [MachineData.setSeg] at h ⊢
  all_goals esim_search

set_option hygiene false in
/-- `esim_search` for the vector operations. -/
local macro "avx_esim_search" : tactic =>
  `(tactic| (
    simp only [AvxOperation.interp, MachineData.setAvxReg, Effects.AllW, Effects.AllEnv] at h ⊢ <;>
    repeat' first
      | exact hk _ _ _ _ _ _ hrel h
      | exact h.elim
      | refine avxOperand_esim hL (fun v r z f D d g hrel h => ?_) hrel h
      | refine avxRegOrMem_esim hL (fun v r z f D d g hrel h => ?_) hrel h
      | refine setAvx_esim hL (fun r z f D d g hrel h => ?_) hrel h
      | refine setAvxLegacy_esim hL (fun r z f D d g hrel h => ?_) hrel h
      | refine rmw16K_esim hL (fun v r z f D d g hrel h => ?_) hrel h
      | refine rmw16Plain_esim hL (fun v r z f D d g hrel h => ?_) hrel h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setAvxReg, Effects.AllW, Effects.AllEnv] at h ⊢))

theorem avxOperation_esim (hL : L.WF) [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w)
    (p : Std.Rco Int64) {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (AvxOperation.interp op p ⟨r, z, f, d⟩ k₁).AllEnv LW g P₁) :
    (AvxOperation.interp op p ⟨r, z, f, D⟩ k₂).AllW L P₂ := by
  cases op <;> avx_esim_search

theorem instr_esim (hL : L.WF) [Labels] (i : Instr) (p : Std.Rco Int64)
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hj : ∀ pc r z f D d g, MemRel L d (gmem L g) D → (j₁ pc ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (j₂ pc ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (i.interp ⟨r, z, f, d⟩ p k₁ j₁).AllEnv LW g P₁) :
    (i.interp ⟨r, z, f, D⟩ p k₂ j₂).AllW L P₂ := by
  cases i with
  | regular asz osz op =>
    simp only [Instr.interp, Effects.AllW, Effects.AllEnv] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact operation_esim hL op p hk hj hrel h
  | avx asz osz aop =>
    simp only [Instr.interp, Effects.AllW, Effects.AllEnv] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact avxOperation_esim hL aop p hk hrel h

theorem directive_esim (hL : L.WF) [Labels] (dir : Directive) (p : Std.Rco Int64)
    {r : Reg64s} {z : RegZmms} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ r z f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, z, f, D⟩).AllW L P₂)
    (hj : ∀ pc r z f D d g, MemRel L d (gmem L g) D → (j₁ pc ⟨r, z, f, d⟩).AllEnv LW g P₁ →
      (j₂ pc ⟨r, z, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (dir.interp ⟨r, z, f, d⟩ p k₁ j₁).AllEnv LW g P₁) :
    (dir.interp ⟨r, z, f, D⟩ p k₂ j₂).AllW L P₂ := by
  cases dir with
  | instr i => exact instr_esim hL i p hk hj hrel h
  | label l => exact hk _ _ _ _ _ _ hrel h
  | byteArray b => exact h.elim

end ESim

/-! ## Instruction steps -/

/-- One instruction in the `lastWrite` environment from a split state is one
merged step, access discipline included, from its merge. -/
theorem instrStepEnv_step1W [_root_.Layout] {L : SharedLayout} (hL : L.WF) {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {x : MachineState × (SharedEnv.lastWrite L).State} {y : MachineState}
    {R : MachineState × (SharedEnv.lastWrite L).State → Prop}
    (hxy : Merged L x y) (h : e.instrStepEnv (SharedEnv.lastWrite L) x R) :
    step1W L e y (fun y' => ∃ x', Merged L x' y' ∧ R x') := by
  obtain ⟨⟨⟨r, z, f, d⟩, pc⟩, g⟩ := x
  obtain ⟨⟨r', z', f', D⟩, pc'⟩ := y
  obtain ⟨hr, hz, hf, hpc, hmr⟩ := hxy
  simp only at hr hz hf hpc hmr
  subst hr hz hf hpc
  have hrel := mergeRel_iff.mp hmr
  obtain ⟨dir, sz, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  letI := _root_.Executable.labels e
  show (Directives.interp (e.directivesAtAddress pc) ⟨r, z, f, D⟩ pc (fun pc s => .done (s, pc))).AllW L _
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]
  unfold Kraken.Executable.stepAtEnv at hstep
  generalize pc + Int64.ofNat sz = pc' at hstep ⊢
  rcases hstep with hstep | hstep
  · refine directive_esim hL dir _ ?_ ?_ hrel hstep
    · intro r z f D d g hrel h
      exact ⟨((⟨r, z, f, d⟩, pc'), g), ⟨rfl, rfl, rfl, rfl, mergeRel_iff.mpr hrel⟩, h⟩
    · intro _ _ _ _ _ _ _ _ h
      exact h.elim
  · refine directive_esim hL dir _ ?_ ?_ hrel hstep
    · intro _ _ _ _ _ _ _ h
      exact h.elim
    · intro pc r z f D d g hrel h
      exact ⟨((⟨r, z, f, d⟩, pc), g), ⟨rfl, rfl, rfl, rfl, mergeRel_iff.mpr hrel⟩, h⟩

/-! ## Link theorems -/

/-- **Shape (ii) recovers shape (i).** -/
theorem lastWrite_to_merged : LastWriteToMerged := by
  intro _ L e _ hL P x y hxy h
  induction h generalizing y with
  | done x hP => exact .done y ⟨x, hxy, hP⟩
  | step x mid hT _ ih =>
    exact .step y _ (instrStepEnv_step1W hL hxy hT) fun y' ⟨x', hx', hm⟩ => ih x' hm y' hx'

theorem memRel_iff_mergeRel : MemRelIffMergeRel :=
  fun _ _ _ _ _ _ henv => memRel_iff_mergeRel_of_envRel henv

/-- **The one-thread link through the environment.** -/
theorem env_link_halt : EnvLinkHalt := by
  intro _ L e _ hL A fuel endPc showPc s pc mem g P hm hsplit henv hPend hstop hev c hc t' ht hend
  obtain ⟨D, hpriv, hsh⟩ := exists_merge hL g s.dmem L fun _ h => h
  have hmr : MergeRel L s.dmem g D := ⟨hpriv, hsplit, hsh⟩
  have hrel : MemRel L s.dmem mem D := (memRel_iff_mergeRel L s.dmem D mem g hL henv).mpr hmr
  obtain ⟨r, z, f, d⟩ := s
  have hev' := lastWrite_to_merged L e hL P _ (⟨r, z, f, D⟩, pc) ⟨rfl, rfl, rfl, rfl, hmr⟩ hev
  obtain ⟨D', hrel', ⟨⟨⟨r', z', f', d'⟩, pc'⟩, g'⟩, ⟨hr, hz, hf, hpc, hmr'⟩, hPx⟩ :=
    merged_link_halt hL A fuel hm hrel (P := fun y' => ∃ x', Merged L x' y' ∧ P x')
      (fun y ⟨x', hx', hPx⟩ => hx'.2.2.2.1.symm.trans (hPend x' hPx)) hstop hev' hc ht hend
  simp only at hr hz hf hpc hmr'
  subst hr hz hf hpc
  have hd : d' = t'.st.st.1.dmem := by
    apply Std.ExtHashMap.ext_getElem?
    intro k
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    by_cases hk : L.Covers k
    · rw [hmr'.split k hk, hrel'.split k hk]
    · rw [← hmr'.priv k hk, ← hrel'.priv k hk]
  subst hd
  refine ⟨g', fun a n ha => ?_, hPx⟩
  have h1 := hmr'.shared a n ha
  rw [hrel'.shared a n ha, sharedBytes] at h1
  exact (toBytes_eq_iff.mp (Option.some.inj h1)).symm

end Kraken.Promising.X64
