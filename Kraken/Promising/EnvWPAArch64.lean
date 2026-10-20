/-
The environment-aware wp and the Promising machine, AArch64: the statements of
the link statements as `Prop` definitions, and their proofs
(`memRel_iff_mergeRel`, `lastWrite_to_merged`, `env_link_halt`). Copied from
x64's `Kraken/Promising/EnvWPX64.lean`, adapted for AArch64. Design note:
`Kraken/Promising/EnvWP.md` §7.

The one-thread instance of `Kraken.AArch64.EnvWP` is `SharedEnv.lastWrite L`:
the environment state is the value of each shared location, which is what the
merged memory of `Kraken.Promising.MergedMem` holds on the footprint. So a
judgment about the *split* state (shared locations out of `dmem`, as the
Promising machine's thread has them) in the `lastWrite` environment is a
judgment about the *merged* state in the `step1W` logic (`LastWriteToMerged`),
and `merged_link_halt` (`Kraken.Promising.SeqLinkAArch64`) takes it the rest
of the way (`EnvLinkHalt`).

The ISA-free part (`envRel`, `MergeRel`, `gmem` and their lemmas,
`exists_merge`) is `Kraken.Promising.EnvMerge`, shared with x64. Everything
here mentions the Promising memory only through it.

There is no `hpres`/`hacc`/`h0` (the access discipline as an invariant, as in
`merged_premises_of_triple`): `AllEnv` in `lastWrite L` refuses every access
that is not exactly a location of `L`, which is the access discipline of
`step1W`. The one hypothesis left is `ValidLayout` (for `instrStep` to
`step1`), as on x64.
-/
import Kraken.AArch64.EnvWP
import Kraken.Promising.EnvMerge
import Kraken.Promising.SeqLinkAArch64Step

open Kraken

namespace Kraken.Promising.AArch64

/-! ## The split state and the merged state -/

/-- The split state `x` (machine state and `lastWrite` environment state) is
the merged state `y`. -/
def Merged (L : SharedLayout) (x : MachineState × (SharedEnv.lastWrite L).State) (y : MachineState) :
    Prop :=
  x.1.1.regs = y.1.regs ∧ x.1.1.status = y.1.status ∧ x.1.2 = y.2 ∧
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

/-! ## The simulation of the split run by the merged run, per primitive

The converse direction of `SeqLinkAArch64`'s `step_sim`: a split state
`⟨r, f, d⟩` in `lastWrite L`'s state `g` whose tree satisfies `AllEnv`, and
the merged state `⟨r, f, D⟩` with `MemRel L d (gmem L g) D`; the merged tree
satisfies `AllW`. The two trees may have different continuations (`k₁`,
`k₂`), related by the continuation hypothesis: one lemma both transports a
cell's step to the interpreter with real continuations (as
`Directive.interp_sound` does) and moves it from the split to the merged
memory. -/

section ESim

variable {L : SharedLayout} {P₁ : MachineState → (BitVec 64 → BitVec 128) → Prop} {P₂ : MachineState → Prop}

local notation "LW" => SharedEnv.lastWrite L

private theorem bits_eq (w : MemWidth) : w.bits = 8 * w.bytes := by cases w <;> rfl

theorem lw_ok_fence (k : FenceKind) (g : BitVec 64 → BitVec 128) : (LW).ok (.fence k) g = True := rfl

theorem lw_step_fence (k : FenceKind) (g g' : BitVec 64 → BitVec 128) (u : Unit) :
    (LW).step (.fence k) g u g' = (g' = g) := rfl

theorem load_esim {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {addr : BitVec 64} {w : MemWidth} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.load ⟨r, f, d⟩ addr w k₁).AllEnv LW g P₁) :
    (MachineData.load ⟨r, f, D⟩ addr w k₂).AllW L P₂ := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    exact hk _ _ _ _ _ _ hrel h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    exact hk _ _ _ _ _ _ hrel (h _ _ ⟨rfl, rfl⟩)

theorem loadK_esim {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.loadK ⟨r, f, d⟩ lk xcl addr w k₁).AllEnv LW g P₁) :
    (MachineData.loadK ⟨r, f, D⟩ lk xcl addr w k₂).AllW L P₂ := by
  unfold MachineData.loadK at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    exact hk _ _ _ _ _ _ hrel h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    exact hk _ _ _ _ _ _ hrel (h _ _ ⟨rfl, rfl⟩)

theorem store_esim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {addr : BitVec 64} {w : MemWidth} {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ r f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.store ⟨r, f, d⟩ addr v k₁).AllEnv LW g P₁) :
    (MachineData.store ⟨r, f, D⟩ addr v k₂).AllW L P₂ := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    exact hk _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    exact hk _ _ _ _ _ (hrel.store_gmem hL hmem (bits_eq w) v) (h true _ (.inl ⟨rfl, rfl⟩))

theorem storeK_esim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v : w.type} {k₁ k₂ : Bool → MachineData → Effects}
    (hk : ∀ b r f D d g, MemRel L d (gmem L g) D → (k₁ b ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ b ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.storeK ⟨r, f, d⟩ sk xcl addr v k₁).AllEnv LW g P₁) :
    (MachineData.storeK ⟨r, f, D⟩ sk xcl addr v k₂).AllW L P₂ := by
  unfold MachineData.storeK at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd : Mem.loadInt d addr w.bytes with
  | some x =>
    rw [hd] at h
    refine ⟨hrel.ok_of_loadInt hd, ?_⟩
    rw [hrel.loadInt_priv hd]
    have hrel' := hrel.store_priv (n := w.bytes) v.toInt (Mem.loadBytes_isSome_of_loadInt hd)
    simp only at h ⊢
    cases xcl with
    | false => exact hk _ _ _ _ _ _ hrel' h
    | true =>
      simp only [ite_true, Effects.AllW, Effects.AllEnv] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ _ _ _ _ hrel' (h true)
      | false => exact hk _ _ _ _ _ _ hrel (h false)
  | none =>
    rw [hd] at h
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, ?_⟩
    rw [hrel.loadInt_gmem hmem]
    have hrel' := hrel.store_gmem hL hmem (bits_eq w) v
    simp only
    cases xcl with
    | false => exact hk _ _ _ _ _ _ hrel' (h true _ (.inl ⟨rfl, rfl⟩))
    | true =>
      simp only [ite_true, Effects.AllW]
      intro b
      cases b with
      | true => exact hk _ _ _ _ _ _ hrel' (h true _ (.inl ⟨rfl, rfl⟩))
      | false => exact hk _ _ _ _ _ _ hrel (h false g (.inr ⟨rfl, rfl, rfl⟩))

theorem rmwK_esim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {rk : Kraken.RmwKind} {nr : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.rmwK ⟨r, f, d⟩ rk nr addr w op k₁).AllEnv LW g P₁) :
    (MachineData.rmwK ⟨r, f, D⟩ rk nr addr w op k₂).AllW L P₂ := by
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
      exact hk _ _ _ _ _ _ (hrel.store_priv _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hop] at h
      exact hk _ _ _ _ _ _ hrel h
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
      have hop' : rmwOpBits w.bits op (g addr) = some (v.setWidth 128) := by simp [rmwOpBits, hop]
      exact hk _ _ _ _ _ _ (hrel.store_gmem hL hmem (bits_eq w) v) (h (g addr) _ ⟨rfl, by rw [hop']⟩)
    | none =>
      have hop' : rmwOpBits w.bits op (g addr) = none := by simp [rmwOpBits, hop]
      exact hk _ _ _ _ _ _ hrel (h (g addr) g ⟨rfl, by rw [hop']⟩)

/-- The pair primitives. A pair with both halves outside `dmem` is `False` in
`AllEnv`, except `CASP` (`rmwPairK_esim`: two per-half `rmw`s, `CaspEnv`); one
with a half in `dmem` is a single access on the other half. -/
theorem loadPairK_esim {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {k₁ k₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ r f D d g, MemRel L d (gmem L g) D → (k₁ v₁ v₂ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v₁ v₂ ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (MachineData.loadPairK ⟨r, f, d⟩ lk xcl addr w k₁).AllEnv LW g P₁) :
    (MachineData.loadPairK ⟨r, f, D⟩ lk xcl addr w k₂).AllW L P₂ := by
  unfold MachineData.loadPairK at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd₁ : Mem.loadInt d addr w.bytes <;> cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv] at h
  · rename_i x₂
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, hrel.ok_of_loadInt hd₂, ?_⟩
    rw [hrel.loadInt_gmem hmem, hrel.loadInt_priv hd₂]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    exact hk _ _ _ _ _ _ _ hrel (h _ _ ⟨rfl, rfl⟩)
  · rename_i x₁
    obtain ⟨hok, h⟩ := h
    have hmem : (addr + w.bytesv, w.bytes) ∈ L := hok
    refine ⟨hrel.ok_of_loadInt hd₁, .inl hmem, ?_⟩
    rw [hrel.loadInt_priv hd₁, hrel.loadInt_gmem hmem]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    exact hk _ _ _ _ _ _ _ hrel (h _ _ ⟨rfl, rfl⟩)
  · refine ⟨hrel.ok_of_loadInt hd₁, hrel.ok_of_loadInt hd₂, ?_⟩
    rw [hrel.loadInt_priv hd₁, hrel.loadInt_priv hd₂]
    exact hk _ _ _ _ _ _ _ hrel h

theorem storePairK_esim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v₁ v₂ : w.type} {k₁ k₂ : Bool → MachineData → Effects}
    (hk : ∀ b r f D d g, MemRel L d (gmem L g) D → (k₁ b ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ b ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D)
    (h : (MachineData.storePairK ⟨r, f, d⟩ sk xcl addr v₁ v₂ k₁).AllEnv LW g P₁) :
    (MachineData.storePairK ⟨r, f, D⟩ sk xcl addr v₁ v₂ k₂).AllW L P₂ := by
  unfold MachineData.storePairK at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd₁ : Mem.loadInt d addr w.bytes <;> cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv] at h
  · -- the low half is shared, the high half private
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, hrel.ok_of_loadInt hd₂, ?_⟩
    rw [hrel.loadInt_gmem hmem, hrel.loadInt_priv hd₂]
    have hrel₁ := hrel.store_gmem hL hmem (bits_eq w) v₁
    have hrel₂ := hrel₁.store_priv (n := w.bytes) v₂.toInt (Mem.loadBytes_isSome_of_loadInt hd₂)
    simp only
    cases xcl with
    | false => exact hk _ _ _ _ _ _ hrel₂ (h true _ (.inl ⟨rfl, rfl⟩))
    | true =>
      simp only [ite_true, Effects.AllW]
      intro b
      cases b with
      | true => exact hk _ _ _ _ _ _ hrel₂ (h true _ (.inl ⟨rfl, rfl⟩))
      | false => exact hk _ _ _ _ _ _ hrel (h false g (.inr ⟨rfl, rfl, rfl⟩))
  · -- the low half is private, the high half shared
    obtain ⟨hok, h⟩ := h
    have hmem : (addr + w.bytesv, w.bytes) ∈ L := hok
    refine ⟨hrel.ok_of_loadInt hd₁, .inl hmem, ?_⟩
    rw [hrel.loadInt_priv hd₁, hrel.loadInt_gmem hmem]
    have hrel₁ := hrel.store_priv (n := w.bytes) v₁.toInt (Mem.loadBytes_isSome_of_loadInt hd₁)
    have hrel₂ := hrel₁.store_gmem hL hmem (bits_eq w) v₂
    simp only
    cases xcl with
    | false => exact hk _ _ _ _ _ _ hrel₂ (h true _ (.inl ⟨rfl, rfl⟩))
    | true =>
      simp only [ite_true, Effects.AllW]
      intro b
      cases b with
      | true => exact hk _ _ _ _ _ _ hrel₂ (h true _ (.inl ⟨rfl, rfl⟩))
      | false => exact hk _ _ _ _ _ _ hrel (h false g (.inr ⟨rfl, rfl, rfl⟩))
  · refine ⟨hrel.ok_of_loadInt hd₁, hrel.ok_of_loadInt hd₂, ?_⟩
    rw [hrel.loadInt_priv hd₁, hrel.loadInt_priv hd₂]
    have hrel₁ := hrel.store_priv (n := w.bytes) v₁.toInt (Mem.loadBytes_isSome_of_loadInt hd₁)
    have hrel₂ := hrel₁.store_priv (n := w.bytes) v₂.toInt
      (Mem.loadBytes_isSome_storeBytes _ _ (Mem.loadBytes_isSome_of_loadInt hd₂))
    simp only at h ⊢
    cases xcl with
    | false => exact hk _ _ _ _ _ _ hrel₂ h
    | true =>
      simp only [ite_true, Effects.AllW, Effects.AllEnv] at h ⊢
      intro b
      cases b with
      | true => exact hk _ _ _ _ _ _ hrel₂ (h true)
      | false => exact hk _ _ _ _ _ _ hrel (h false)

theorem rmwPairK_esim (hL : L.WF) {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {k₁ k₂ : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ r f D d g, MemRel L d (gmem L g) D → (k₁ v₁ v₂ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v₁ v₂ ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D)
    (h : (MachineData.rmwPairK ⟨r, f, d⟩ rk addr c₁ c₂ n₁ n₂ k₁).AllEnv LW g P₁) :
    (MachineData.rmwPairK ⟨r, f, D⟩ rk addr c₁ c₂ n₁ n₂ k₂).AllW L P₂ := by
  unfold MachineData.rmwPairK at h ⊢
  simp only [Effects.AllW, Effects.AllEnv] at h ⊢
  cases hd₁ : Mem.loadInt d addr w.bytes <;> cases hd₂ : Mem.loadInt d (addr + w.bytesv) w.bytes <;>
    rw [hd₁, hd₂] at h <;> simp only [Effects.AllEnv] at h
  · -- both halves shared: `CaspEnv` in `lastWrite` reads both and, on a match,
    -- writes both, as `rmwPairK` does on mapped memory
    obtain ⟨hm₁, hm₂, h⟩ := SharedEnv.lastWrite_caspEnv_iff.mp h
    unfold SharedEnv.caspLW at h
    refine ⟨.inl hm₁, .inl hm₁, .inl hm₂, .inl hm₂, ?_⟩
    rw [hrel.loadInt_gmem hm₁, hrel.loadInt_gmem hm₂]
    simp only
    rw [sharedBytes_gmem hm₁ (bits_eq w), sharedBytes_gmem hm₂ (bits_eq w)]
    by_cases hc : ((g addr).setWidth w.bits == c₁ && (g (addr + w.bytesv)).setWidth w.bits == c₂) = true
    · simp only [hc, ite_true] at h ⊢
      exact hk _ _ _ _ _ _ _ ((hrel.store_gmem hL hm₁ (bits_eq w) n₁).store_gmem hL hm₂ (bits_eq w) n₂) h
    · simp only [hc, ite_false, Bool.false_eq_true] at h ⊢
      exact hk _ _ _ _ _ _ _ hrel h
  · -- the low half is shared, the high half private
    rename_i x₂
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, w.bytes) ∈ L := hok
    refine ⟨.inl hmem, .inl hmem, hrel.ok_of_loadInt hd₂, hrel.ok_of_loadInt hd₂, ?_⟩
    rw [hrel.loadInt_gmem hmem, hrel.loadInt_priv hd₂]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    by_cases hc : ((g addr).setWidth w.bits == c₁ && (BitVec.ofInt w.bits x₂ : w.type) == c₂) = true
    · have hop : rmwOpBits w.bits (fun o₁ => if (o₁ == c₁ && (BitVec.ofInt w.bits x₂ : w.type) == c₂) = true
          then some n₁ else none) (g addr) = some (n₁.setWidth 128) := by simp [rmwOpBits, hc]
      have h' := h (g addr) (SharedEnv.upd g addr (n₁.setWidth 128)) ⟨rfl, by rw [hop]⟩
      simp only [hc, ite_true] at h' ⊢
      have hrel₁ := hrel.store_gmem hL hmem (bits_eq w) n₁
      exact hk _ _ _ _ _ _ _ (hrel₁.store_priv (n := w.bytes) n₂.toInt (Mem.loadBytes_isSome_of_loadInt hd₂)) h'
    · have hop : rmwOpBits w.bits (fun o₁ => if (o₁ == c₁ && (BitVec.ofInt w.bits x₂ : w.type) == c₂) = true
          then some n₁ else none) (g addr) = none := by simp [rmwOpBits, hc]
      have h' := h (g addr) g ⟨rfl, by rw [hop]⟩
      simp only [hc, ite_false, Bool.false_eq_true] at h' ⊢
      exact hk _ _ _ _ _ _ _ hrel h'
  · -- the low half is private, the high half shared
    rename_i x₁
    obtain ⟨hok, h⟩ := h
    have hmem : (addr + w.bytesv, w.bytes) ∈ L := hok
    refine ⟨hrel.ok_of_loadInt hd₁, hrel.ok_of_loadInt hd₁, .inl hmem, .inl hmem, ?_⟩
    rw [hrel.loadInt_priv hd₁, hrel.loadInt_gmem hmem]
    simp only
    rw [sharedBytes_gmem hmem (bits_eq w)]
    by_cases hc : ((BitVec.ofInt w.bits x₁ : w.type) == c₁ && (g (addr + w.bytesv)).setWidth w.bits == c₂) = true
    · have hop : rmwOpBits w.bits (fun o₂ => if ((BitVec.ofInt w.bits x₁ : w.type) == c₁ && o₂ == c₂) = true
          then some n₂ else none) (g (addr + w.bytesv)) = some (n₂.setWidth 128) := by simp [rmwOpBits, hc]
      have h' := h (g (addr + w.bytesv)) (SharedEnv.upd g (addr + w.bytesv) (n₂.setWidth 128)) ⟨rfl, by rw [hop]⟩
      simp only [hc, ite_true] at h' ⊢
      have hrel₁ := hrel.store_priv (n := w.bytes) n₁.toInt (Mem.loadBytes_isSome_of_loadInt hd₁)
      exact hk _ _ _ _ _ _ _ (hrel₁.store_gmem hL hmem (bits_eq w) n₂) h'
    · have hop : rmwOpBits w.bits (fun o₂ => if ((BitVec.ofInt w.bits x₁ : w.type) == c₁ && o₂ == c₂) = true
          then some n₂ else none) (g (addr + w.bytesv)) = none := by simp [rmwOpBits, hc]
      have h' := h (g (addr + w.bytesv)) g ⟨rfl, by rw [hop]⟩
      simp only [hc, ite_false, Bool.false_eq_true] at h' ⊢
      exact hk _ _ _ _ _ _ _ hrel h'
  · refine ⟨hrel.ok_of_loadInt hd₁, hrel.ok_of_loadInt hd₁, hrel.ok_of_loadInt hd₂, hrel.ok_of_loadInt hd₂, ?_⟩
    rw [hrel.loadInt_priv hd₁, hrel.loadInt_priv hd₂]
    simp only at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      have hrel₁ := hrel.store_priv (n := w.bytes) n₁.toInt (Mem.loadBytes_isSome_of_loadInt hd₁)
      exact hk _ _ _ _ _ _ _ (hrel₁.store_priv (n := w.bytes) n₂.toInt
        (Mem.loadBytes_isSome_storeBytes _ _ (Mem.loadBytes_isSome_of_loadInt hd₂))) h
    · rename_i hc; rw [if_neg hc]; exact hk _ _ _ _ _ _ _ hrel h

/-! ### Per addressing form -/

theorem AddrExpr.checkSPAlignment_esim {a : AddrExpr} {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {ok₁ ok₂ : Unit → Effects}
    (hk : (ok₁ ()).AllEnv LW g P₁ → (ok₂ ()).AllW L P₂)
    (h : (a.checkSPAlignment ⟨r, f, d⟩ ok₁).AllEnv LW g P₁) : (a.checkSPAlignment ⟨r, f, D⟩ ok₂).AllW L P₂ := by
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

theorem UnscaledAddrExpr.checkSPAlignment_esim {a : UnscaledAddrExpr} {r : Reg64s} {f : StatusFlags}
    {D d : DataMem} {g : BitVec 64 → BitVec 128} {ok₁ ok₂ : Unit → Effects}
    (hk : (ok₁ ()).AllEnv LW g P₁ → (ok₂ ()).AllW L P₂)
    (h : (a.checkSPAlignment ⟨r, f, d⟩ ok₁).AllEnv LW g P₁) : (a.checkSPAlignment ⟨r, f, D⟩ ok₂).AllW L P₂ := by
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

theorem interpBase_esim {base : RegOrSp .W64} {r : Reg64s} {f : StatusFlags} {D d : DataMem}
    {g : BitVec 64 → BitVec 128} {ok₁ ok₂ : BitVec 64 → Effects}
    (hk : ∀ a, (ok₁ a).AllEnv LW g P₁ → (ok₂ a).AllW L P₂)
    (h : (base.interpBase ⟨r, f, d⟩ ok₁).AllEnv LW g P₁) : (base.interpBase ⟨r, f, D⟩ ok₂).AllW L P₂ := by
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

theorem AddrExpr.interpLoad_esim [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64} {r : Reg64s}
    {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (a.interpLoad ⟨r, f, d⟩ p k₁).AllEnv LW g P₁) :
    (a.interpLoad ⟨r, f, D⟩ p k₂).AllW L P₂ := by
  unfold AddrExpr.interpLoad at h ⊢
  refine AddrExpr.checkSPAlignment_esim (fun h => ?_) h
  simp only [AddrExpr.eval_mk] at h ⊢
  exact load_esim hk hrel h

theorem AddrExpr.interpStore_esim (hL : L.WF) [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64}
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ r f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (a.interpStore ⟨r, f, d⟩ p v k₁).AllEnv LW g P₁) :
    (a.interpStore ⟨r, f, D⟩ p v k₂).AllW L P₂ := by
  unfold AddrExpr.interpStore at h ⊢
  refine AddrExpr.checkSPAlignment_esim (fun h => ?_) h
  simp only [AddrExpr.eval_mk] at h ⊢
  exact store_esim hL hk hrel h

theorem UnscaledAddrExpr.interpLoad_esim [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (a.interpLoad ⟨r, f, d⟩ p k₁).AllEnv LW g P₁) :
    (a.interpLoad ⟨r, f, D⟩ p k₂).AllW L P₂ := by
  unfold UnscaledAddrExpr.interpLoad at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_esim (fun h => ?_) h
  exact load_esim hk hrel h

theorem UnscaledAddrExpr.interpStore_esim (hL : L.WF) [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {v : w.type} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ r f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (a.interpStore ⟨r, f, d⟩ p v k₁).AllEnv LW g P₁) :
    (a.interpStore ⟨r, f, D⟩ p v k₂).AllW L P₂ := by
  unfold UnscaledAddrExpr.interpStore at h ⊢
  refine UnscaledAddrExpr.checkSPAlignment_esim (fun h => ?_) h
  exact store_esim hL hk hrel h

theorem AddrOrLit.interpLoad_esim [Labels] {w : MemWidth} {a : AddrOrLit} {p : Std.Rco Int64}
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v r f D d g, MemRel L d (gmem L g) D → (k₁ v ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ v ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (a.interpLoad ⟨r, f, d⟩ p k₁).AllEnv LW g P₁) :
    (a.interpLoad ⟨r, f, D⟩ p k₂).AllW L P₂ := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_esim hk hrel h
  | lit l =>
    cases l with
    | addr a => exact load_esim hk hrel h
    | pool q => exact hk _ _ _ _ _ _ hrel h

/-! ### Per instruction -/

/- As in `SeqLinkAArch64`: the dictionary lemmas are applied by search, the
primitives they are keyed on sealed. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK MachineData.storeK
  MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK AddrExpr.interpLoad
  AddrExpr.interpStore UnscaledAddrExpr.interpLoad
  UnscaledAddrExpr.interpStore AddrOrLit.interpLoad AddrExpr.checkSPAlignment RegOrSp.interpBase

set_option hygiene false in
/-- Reduce the interpreter on both sides and apply the dictionary until the
continuation hypotheses `hk`/`hj` close every leaf. -/
local macro "esim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllW,
      Effects.AllEnv, AddrExpr.eval_mk, lw_ok_fence, lw_step_fence, true_and, forall_eq'] at h ⊢ <;>
    repeat' first
      | exact hk _ _ _ _ _ hrel h
      | exact hj _ _ _ _ _ _ hrel h
      | exact hk _ _ _ _ _ hrel (h g rfl)
      | exact h.elim
      | refine AddrOrLit.interpLoad_esim (fun v r f D d g hrel h => ?_) hrel h
      | refine AddrExpr.interpLoad_esim (fun v r f D d g hrel h => ?_) hrel h
      | refine UnscaledAddrExpr.interpLoad_esim (fun v r f D d g hrel h => ?_) hrel h
      | refine AddrExpr.interpStore_esim hL (fun r f D d g hrel h => ?_) hrel h
      | refine UnscaledAddrExpr.interpStore_esim hL (fun r f D d g hrel h => ?_) hrel h
      | refine AddrExpr.checkSPAlignment_esim (fun h => ?_) h
      | refine load_esim (fun v r f D d g hrel h => ?_) hrel h
      | refine store_esim hL (fun r f D d g hrel h => ?_) hrel h
      | refine loadK_esim (fun v r f D d g hrel h => ?_) hrel h
      | refine storeK_esim hL (fun b r f D d g hrel h => ?_) hrel h
      | refine rmwK_esim hL (fun v r f D d g hrel h => ?_) hrel h
      | refine loadPairK_esim (fun v₁ v₂ r f D d g hrel h => ?_) hrel h
      | refine storePairK_esim hL (fun b r f D d g hrel h => ?_) hrel h
      | refine rmwPairK_esim hL (fun v₁ v₂ r f D d g hrel h => ?_) hrel h
      | refine interpBase_esim (fun a h => ?_) h
      | (refine fun v => ?_; specialize h v)
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.AllW, Effects.AllEnv,
          AddrExpr.eval_mk, lw_ok_fence, lw_step_fence, true_and, forall_eq'] at h ⊢))

theorem operation_esim (hL : L.WF) [Labels] {w : RegWidth} (op : Operation w) (p : Std.Rco Int64)
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ r f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, f, D⟩).AllW L P₂)
    (hj : ∀ pc r f D d g, MemRel L d (gmem L g) D → (j₁ pc ⟨r, f, d⟩).AllEnv LW g P₁ →
      (j₂ pc ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (Operation.interp op p ⟨r, f, d⟩ k₁ j₁).AllEnv LW g P₁) :
    (Operation.interp op p ⟨r, f, D⟩ k₂ j₂).AllW L P₂ := by
  cases op <;> esim_search

theorem instr_esim (hL : L.WF) [Labels] (i : Instr) (p : Std.Rco Int64)
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ r f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, f, D⟩).AllW L P₂)
    (hj : ∀ pc r f D d g, MemRel L d (gmem L g) D → (j₁ pc ⟨r, f, d⟩).AllEnv LW g P₁ →
      (j₂ pc ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (i.interp ⟨r, f, d⟩ p k₁ j₁).AllEnv LW g P₁) :
    (i.interp ⟨r, f, D⟩ p k₂ j₂).AllW L P₂ := by
  unfold Instr.interp at h ⊢
  exact operation_esim hL _ _ hk hj hrel h

theorem directive_esim (hL : L.WF) [Labels] (dir : Directive) (p : Std.Rco Int64)
    {r : Reg64s} {f : StatusFlags} {D d : DataMem} {g : BitVec 64 → BitVec 128}
    {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ r f D d g, MemRel L d (gmem L g) D → (k₁ ⟨r, f, d⟩).AllEnv LW g P₁ →
      (k₂ ⟨r, f, D⟩).AllW L P₂)
    (hj : ∀ pc r f D d g, MemRel L d (gmem L g) D → (j₁ pc ⟨r, f, d⟩).AllEnv LW g P₁ →
      (j₂ pc ⟨r, f, D⟩).AllW L P₂)
    (hrel : MemRel L d (gmem L g) D) (h : (dir.interp ⟨r, f, d⟩ p k₁ j₁).AllEnv LW g P₁) :
    (dir.interp ⟨r, f, D⟩ p k₂ j₂).AllW L P₂ := by
  cases dir with
  | instr i => exact instr_esim hL i p hk hj hrel h
  | label l => exact hk _ _ _ _ _ hrel h
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
  obtain ⟨⟨⟨r, f, d⟩, pc⟩, g⟩ := x
  obtain ⟨⟨r', f', D⟩, pc'⟩ := y
  obtain ⟨hr, hf, hpc, hmr⟩ := hxy
  simp only at hr hf hpc hmr
  subst hr hf hpc
  have hrel := mergeRel_iff.mp hmr
  obtain ⟨dir, sz, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  letI := _root_.Executable.labels e
  show (Directives.interp (e.directivesAtAddress pc) ⟨r, f, D⟩ pc (fun pc s => .done (s, pc))).AllW L _
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]
  unfold Kraken.Executable.stepAtEnv at hstep
  generalize pc + Int64.ofNat sz = pc' at hstep ⊢
  rcases hstep with hstep | hstep
  · refine directive_esim hL dir _ ?_ ?_ hrel hstep
    · intro r f D d g hrel h
      exact ⟨((⟨r, f, d⟩, pc'), g), ⟨rfl, rfl, rfl, mergeRel_iff.mpr hrel⟩, h⟩
    · intro _ _ _ _ _ _ _ h
      exact h.elim
  · refine directive_esim hL dir _ ?_ ?_ hrel hstep
    · intro _ _ _ _ _ _ h
      exact h.elim
    · intro pc r f D d g hrel h
      exact ⟨((⟨r, f, d⟩, pc), g), ⟨rfl, rfl, rfl, mergeRel_iff.mpr hrel⟩, h⟩

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
  obtain ⟨r, f, d⟩ := s
  have hev' := lastWrite_to_merged L e hL P _ (⟨r, f, D⟩, pc) ⟨rfl, rfl, rfl, hmr⟩ hev
  obtain ⟨D', hrel', ⟨⟨⟨r', f', d'⟩, pc'⟩, g'⟩, ⟨hr, hf, hpc, hmr'⟩, hPx⟩ :=
    merged_link_halt hL A fuel hm hrel (P := fun y' => ∃ x', Merged L x' y' ∧ P x')
      (fun y ⟨x', hx', hPx⟩ => hx'.2.2.1.symm.trans (hPend x' hPx)) hstop hev' hc ht hend
  simp only at hr hf hpc hmr'
  subst hr hf hpc
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

end Kraken.Promising.AArch64
