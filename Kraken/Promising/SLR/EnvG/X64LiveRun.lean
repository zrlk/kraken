/-
EnvG on x64: **the x64 run lemma**, the x64
analogue of `EnvSpikeA64.exec_treeJ_of_instrStepEnv` and of
`A64Live.exec_treeJLive_of_instrStepEnv(')`.

`InvLinkX64.lean`'s simulation (`isim`) is stated for `SharedEnv.inv S G`
and `EvTree.AllInv` only; there is no ISA-generic x64 counterpart of
`EnvSpikeA64.jsim`. This file is that counterpart: `InvLinkX64`'s `isim`
with `AllInv` replaced by an arbitrary tree judgment `J : EnvSpike.TreeJ E`
and the environment state threaded through (the A64 prototype's `jsim`
pattern).

## The x64 side conditions

x64 needs the two side conditions of `InvLinkX64` (see there): the adapter's
non-atomic vector accesses are mapped-first per 8-byte piece while `AllEnv`
sends every piece of an unmapped access to the environment, and an `atomic`
vector access is one event only at 16 bytes. For a generic environment they
are stated against a layout `S`:

- `Split S d` (the private memory maps no byte of a location of `S`) and
  `Le16 S` (`InvLinkX64`);
- `X64Fit S E`: every plain non-exclusive load or store the environment
  permits is exactly a location of `S`. `inv S G` satisfies it; an
  environment that permits every load (`EnvG`, `relPure`) does not, so it is
  restricted to `S` first: **`SharedEnv.within E S`** (same state and
  outcomes, `ok` additionally asks that every access be a location of `S`;
  `within_fit`). A judgment `J` of `E` is one of `E.within S`
  (`TreeJ.toWithin`, `TreeJLive.toWithin`).

## Results

- `exec_treeJ_of_instrStepEnv` (x64, `Kraken.Promising.X64.EnvG`): one
  `instrStepEnv E` step from a thread state with no declarations and a split
  private memory makes the thread's tree satisfy `J`, with `J.Post` at the
  leaves, whose private memory is still split.
- `exec_treeJLive_of_instrStepEnv`: the same for a live judgment
  (`EnvG.TreeJLive`); no static check, every x64 tree is live
  (`X64Live.exec_rmwLive`).
- `exec_treeJLive_of_instrStepEnvW`: the same from a step of `E.within S`
  for a live judgment of `E` (the form `X64Link.lean` uses).

Phase 1: single-access trees; the lemmas here hold
for every tree.
-/
import Kraken.Promising.InvLinkX64
import Kraken.Promising.SLR.EnvG.X64Live

open Kraken

/-! ## Restricting an environment to a layout -/

namespace Kraken.SharedEnv

open Kraken.Promising (Loc Val)

/-- An access is exactly a location of `S` (fences always are). -/
def AccessIn (S : Layout) : SharedAccess → Prop
  | .load _ _ addr n => (addr, n) ∈ S
  | .store _ _ addr n _ => (addr, n) ∈ S
  | .rmw _ addr n _ => (addr, n) ∈ S
  | .fence _ => True

/-- **`E` restricted to the layout `S`**: the same state and outcomes; an
access is permitted if `E` permits it and it is exactly a location of `S`.
The access discipline of `inv S G`, on top of any environment. -/
def within (E : SharedEnv) (S : Layout) : SharedEnv where
  State := E.State
  ok a g := E.ok a g ∧ AccessIn S a
  step := E.step

variable {E : SharedEnv} {S : Layout}

@[simp] theorem within_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {g : (E.within S).State} :
    (E.within S).ok (.load k xcl addr n) g ↔ E.ok (.load k xcl addr n) g ∧ (addr, n) ∈ S := Iff.rfl

@[simp] theorem within_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : BitVec 128}
    {g : (E.within S).State} :
    (E.within S).ok (.store k xcl addr n v) g ↔ E.ok (.store k xcl addr n v) g ∧ (addr, n) ∈ S := Iff.rfl

@[simp] theorem within_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g : (E.within S).State} :
    (E.within S).ok (.rmw k addr n op) g ↔ E.ok (.rmw k addr n op) g ∧ (addr, n) ∈ S := Iff.rfl

@[simp] theorem within_ok_fence {k : FenceKind} {g : (E.within S).State} :
    (E.within S).ok (.fence k) g ↔ E.ok (.fence k) g := and_iff_left trivial

@[simp] theorem within_step {a : SharedAccess} {g g' : (E.within S).State} {r : a.Ret} :
    (E.within S).step a g r g' ↔ E.step a g r g' := Iff.rfl

/-- Restricting keeps `FencesSkip`. -/
theorem within_fencesSkip (h : E.FencesSkip) : (E.within S).FencesSkip :=
  fun k g => ⟨⟨(h k g).1, trivial⟩, (h k g).2⟩

instance [E.Skips] : (E.within S).Skips := ⟨within_fencesSkip Skips.fencesSkip⟩

end Kraken.SharedEnv

namespace Kraken.Promising.X64

open Kraken.Promising.SLR.EnvSpike

/-- **The x64 fit of an environment to a layout**: every plain
non-exclusive load or store it permits is exactly a location of `S` (the
accesses `AllEnv` makes of the pieces of a non-atomic vector access and of a
guaranteed-atomic one). -/
structure X64Fit (S : SharedEnv.Layout) (E : SharedEnv) : Prop where
  load : ∀ {addr : BitVec 64} {n : Nat} {g : E.State}, E.ok (.load .plain false addr n) g → (addr, n) ∈ S
  store : ∀ {addr : BitVec 64} {n : Nat} {v : BitVec 128} {g : E.State},
    E.ok (.store .plain false addr n v) g → (addr, n) ∈ S

/-- A restricted environment fits its layout. -/
theorem within_fit (E : SharedEnv) (S : SharedEnv.Layout) : X64Fit S (E.within S) :=
  ⟨fun h => h.2, fun h => h.2⟩

/-- The invariant environment fits its layout. -/
theorem inv_fit (S : SharedEnv.Layout) (G : Loc → Val → Prop) : X64Fit S (SharedEnv.inv S G) :=
  ⟨fun h => h, fun h => h.1⟩

/-- A tree judgment of `E` is one of `E` restricted to `S` (its laws are
asked for fewer accesses). -/
def _root_.Kraken.Promising.SLR.EnvSpike.TreeJ.toWithin {E : SharedEnv} {σ : Type} (J : TreeJ E σ)
    (S : SharedEnv.Layout) : TreeJ (E.within S) σ where
  W := J.W
  Post := J.Post
  done := J.done
  fault := J.fault
  choose := J.choose
  load h₁ h₂ := J.load h₁.1 h₂
  store h₁ h₂ := J.store h₁.1 h₂
  rmw h₁ h₂ := J.rmw h₁.1 h₂
  fence h₁ h₂ := J.fence h₁.1 h₂

private theorem w128_of_le16' {S : SharedEnv.Layout} (hS : Le16 S) {addr : BitVec 64} {w : AvxWidth}
    (h : (addr, w.bytes) ∈ S) : w = .W128 := by
  have := hS _ h
  cases w <;> simp_all [AvxWidth.bytes]

private theorem avx_bytes_eq'' (w : AvxWidth) : w.bytes = 8 * (w.bytes / 8) := by cases w <;> rfl

namespace EnvG

/-! ## The simulation, per primitive -/

section JSim

variable {E : SharedEnv} (J : TreeJ E MachineState) {S : SharedEnv.Layout} (hF : X64Fit S E)
  {P₁ : MachineState → E.State → Prop}

include hF in
/-- The pieces of a non-atomic vector load: under `Split` and the fit, every
piece the environment answers is unmapped, so the adapter makes each an
event. -/
theorem loadPieces_jsim {d : DataMem} (hs : Split S d) :
    ∀ (n : Nat) (addr : BitVec 64) (g : E.State) (K : List (BitVec 64) → E.State → Prop)
      (k : List UInt8 → EvTree MachineState),
      E.LoadPieces addr n g K →
      (∀ (vs : List (BitVec 128)) g', K (vs.map (·.setWidth 64)) g' → J.W (k (piecesBytes vs)) g') →
      J.W (loadPieces {} d addr n k) g
  | 0, _, g, _, _, h, hk => hk [] g h
  | n + 1, addr, g, K, k, h, hk => by
    obtain ⟨hok, h⟩ := h
    unfold loadPieces
    rw [hs.piece_none (hF.load hok)]
    simp only
    split
    · exact J.fault
    · simp only [EvTree.access_empty]
      exact J.load hok fun v g' hv =>
        loadPieces_jsim hs n (addr + 8) g' _ _ (h v g' hv) fun vs g'' hK => hk (v :: vs) g'' hK

include hF in
/-- The pieces of a non-atomic vector store: under `Split` and the fit, every
piece is an event, and the private memory is unchanged. -/
theorem storePieces_jsim {d : DataMem} (hs : Split S d) :
    ∀ (ps : List (BitVec 64)) (addr : BitVec 64) (g : E.State) (K : E.State → Prop)
      (k : DataMem → EvTree MachineState),
      E.StorePieces addr ps g K → (∀ g', K g' → J.W (k d) g') →
      J.W (storePieces {} addr ps.length (ps.flatMap fun p => Int.toBytes 8 p.toInt) d k) g
  | [], _, g, _, _, h, hk => hk g h
  | p :: ps, addr, g, K, k, h, hk => by
    obtain ⟨hok, h⟩ := h
    simp only [List.length_cons]
    unfold storePieces
    rw [hs.piece_none (hF.store hok)]
    simp only
    split
    · exact J.fault
    · have htake : (List.flatMap (fun p => Int.toBytes 8 p.toInt) (p :: ps)).take 8 = Int.toBytes 8 p.toInt := by
        rw [List.flatMap_cons, List.take_left' (Int.toBytes_length 8 _)]
      have hdrop : (List.flatMap (fun p => Int.toBytes 8 p.toInt) (p :: ps)).drop 8 =
          ps.flatMap fun p => Int.toBytes 8 p.toInt := by
        rw [List.flatMap_cons, List.drop_left' (Int.toBytes_length 8 _)]
      simp only [EvTree.access_empty, htake, hdrop, pieceVal_toBytes]
      exact J.store hok fun b g' hb => storePieces_jsim hs ps (addr + 8) g' K k (h b g' hb) hk

/-- `undefined`: a Boolean is a `choose` of the adapter; any other kind of
value is a fault. -/
theorem undefined_jsim {α : Type} {inst : NondetSupportingType α} {ret₁ ret₂ : α → Effects} {g : E.State}
    (hk : ∀ v, (ret₁ v).AllEnv E g P₁ → J.W (toEv {} (ret₂ v)) g)
    (h : ∀ v, (ret₁ v).AllEnv E g P₁) : J.W (toEv {} (Effects.undefined ret₂)) g := by
  cases inst <;> simp only [toEv]
  all_goals first | exact J.fault | exact J.choose fun i => hk _ (h _)

theorem load_jsim {s : MachineData} {addr : BitVec 64} {w : Width} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.load s addr w k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.load s addr w k₂)) g := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ _ hs h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.load h.1 fun v g' hv => hk _ _ _ hs (h.2 v g' hv)

theorem store_jsim {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.store s addr v k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.store s addr v k₂)) g := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.store h.1 fun b g' hb => hk _ _ hs (h.2 b g' hb)

theorem storeNT_jsim {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.storeNT s addr v k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.storeNT s addr v k₂)) g := by
  unfold MachineData.storeNT at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.store h.1 fun b g' hb => hk _ _ hs (h.2 b g' hb)

theorem rmwK_jsim {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.rmwK s rk addr w op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmwK s rk addr w op k₂)) g := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt w.bits x) <;> rw [hop] at h
    · exact hk _ _ _ hs h
    · exact hk _ _ _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.rmw h.1 fun old g' hold => hk _ _ _ hs (h.2 old g' hold)

theorem rmwPlain_jsim {s : MachineData} {addr : BitVec 64} {w : Width} {op : w.type → Option w.type}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.rmwPlain s addr w op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmwPlain s addr w op k₂)) g := by
  unfold MachineData.rmwPlain at h ⊢
  refine load_jsim J (fun v s g hs h => ?_) hs h
  cases hop : op v with
  | some new =>
    simp only [hop] at h ⊢
    exact store_jsim J (fun s g hs h => hk _ _ _ hs h) hs h
  | none =>
    simp only [hop] at h ⊢
    exact hk _ _ _ hs h

include hF in
theorem loadAvx_jsim (hS : Le16 S) {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {k₁ k₂ : w.type → MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.loadAvx s addr w k₁ checkAlign atomic).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.loadAvx s addr w k₂ checkAlign atomic)) g := by
  unfold MachineData.loadAvx at h ⊢
  split
  · simp only [toEv]; exact J.fault
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllEnv, toEv] at h ⊢
    cases hd : Mem.loadInt s.dmem addr w.bytes with
    | some x => rw [hd] at h; exact hk _ _ _ hs h
    | none =>
      rw [hd] at h
      cases atomic with
      | true =>
        simp only [Effects.AllEnv] at h
        obtain ⟨hok, h⟩ := h
        obtain rfl := w128_of_le16' hS (hF.load hok)
        simp only [toEv, Bool.true_and, EvTree.access_empty]
        exact J.load hok fun v g' hv => hk _ _ _ hs (h v g' hv)
      | false =>
        simp only [Effects.AllEnv] at h
        simp only [toEv, Bool.false_and, Bool.false_eq_true, ite_false]
        refine loadPieces_jsim J hF hs _ addr g _ _ h fun vs g' hK => ?_
        rw [ofInt_ofBytes_piecesBytes]
        exact hk _ _ _ hs hK

include hF in
theorem storeAvx_jsim (hS : Le16 S) {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type}
    {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.storeAvx s addr v k₁ checkAlign atomic).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.storeAvx s addr v k₂ checkAlign atomic)) g := by
  unfold MachineData.storeAvx at h ⊢
  split
  · simp only [toEv]; exact J.fault
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllEnv, toEv] at h ⊢
    cases hd : Mem.loadInt s.dmem addr w.bytes with
    | some x => rw [hd] at h; exact hk _ _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hd] at h
      cases atomic with
      | true =>
        simp only [Effects.AllEnv] at h
        obtain ⟨hok, h⟩ := h
        obtain rfl := w128_of_le16' hS (hF.store hok)
        simp only [toEv, Bool.true_and, EvTree.access_empty]
        exact J.store hok fun b g' hb => hk _ _ hs (h b g' hb)
      | false =>
        simp only [Effects.AllEnv] at h
        simp only [toEv, Bool.false_and, Bool.false_eq_true, ite_false]
        have hb : Int.toBytes w.bytes v.toInt = (toPieces v (w.bytes / 8)).flatMap fun p => Int.toBytes 8 p.toInt := by
          rw [← toBytes_toPieces (by cases w <;> rfl) v, ← avx_bytes_eq'' w]
        rw [hb]
        have hl := length_toPieces v (w.bytes / 8)
        have := storePieces_jsim J hF hs (toPieces v (w.bytes / 8)) addr g _
          (fun d => toEv {} (k₂ { s with dmem := d })) h (fun g' hK => hk _ _ hs hK)
        rwa [hl] at this

theorem rmw16K_jsim {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {k₁ k₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.rmw16K s rk addr op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmw16K s rk addr op k₂)) g := by
  unfold MachineData.rmw16K at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr 16 with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt 128 x) <;> rw [hop] at h
    · exact hk _ _ _ hs h
    · exact hk _ _ _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty] at h ⊢
    exact J.rmw h.1 fun old g' hold => hk _ _ _ hs (h.2 old g' hold)

include hF in
theorem rmw16Plain_jsim (hS : Le16 S) {s : MachineData} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {k₁ k₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.rmw16Plain s addr op k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.rmw16Plain s addr op k₂)) g := by
  unfold MachineData.rmw16Plain at h ⊢
  refine loadAvx_jsim J hF hS (fun v s g hs h => ?_) hs h
  cases hop : op v with
  | some new =>
    simp only [hop] at h ⊢
    exact storeAvx_jsim J hF hS (fun s g hs h => hk _ _ _ hs h) hs h
  | none =>
    simp only [hop] at h ⊢
    exact hk _ _ _ hs h

/-! ### Operands -/

include hF in
theorem avxRegOrMem_jsim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {o : AvxRegOrMem w}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (o.interp s p k₁ checkAlign atomic).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂ checkAlign atomic)) g := by
  cases o with
  | avx x => exact hk _ _ _ hs h
  | mem a => exact loadAvx_jsim J hF hS hk hs h

include hF in
theorem avxOperand_jsim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {o : AvxOperand w}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign : Bool}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (o.interp s p k₁ checkAlign).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂ checkAlign)) g := by
  cases o with
  | regOrMem rm => exact avxRegOrMem_jsim J hF hS hk hs h

include hF in
theorem setAvx_jsim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.setAvx s dst v p k₁ checkAlign atomic).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.setAvx s dst v p k₂ checkAlign atomic)) g := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvx, MachineData.setAvxReg] at h ⊢
    exact hk _ _ hs h
  | mem a => exact storeAvx_jsim J hF hS hk hs h

include hF in
theorem setAvxLegacy_jsim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hs : Split S s.dmem) {g : E.State}
    (h : (MachineData.setAvxLegacy s dst v p k₁ checkAlign atomic).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.setAvxLegacy s dst v p k₂ checkAlign atomic)) g := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvxLegacy, MachineData.setAvxLegacyReg] at h ⊢
    exact hk _ _ hs h
  | mem a => exact storeAvx_jsim J hF hS hk hs h

theorem regOrMem_jsim [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (o.interp s p k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂)) g := by
  cases o with
  | reg x => exact hk _ _ _ hs h
  | mem a => exact load_jsim J hk hs h

theorem operand_jsim [Labels] [AddressSize] {w : Width} {o : Operand w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (o.interp s p k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂)) g := by
  cases o with
  | regOrMem rm => exact regOrMem_jsim J hk hs h
  | imm v => exact hk _ _ _ hs h

theorem relRegOrMem_jsim [Labels] [AddressSize] {o : RelRegOrMem} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : BitVec 64 → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (o.interp s p k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.interp s p k₂)) g := by
  cases o with
  | rel c => exact hk _ _ _ hs h
  | reg x => exact hk _ _ _ hs h
  | mem a => exact load_jsim J hk hs h

theorem set_jsim [Labels] [AddressSize] {w : Width} {dst : Dst w} {v : w.type} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (MachineData.set s dst v p k₁).AllEnv E g P₁) :
    J.W (toEv {} (MachineData.set s dst v p k₂)) g := by
  cases dst with
  | reg x =>
    simp only [MachineData.set, MachineData.setReg] at h ⊢
    exact hk _ _ hs h
  | mem a => exact store_jsim J hk hs h

theorem rmw_jsim [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {lock : Bool}
    {p : Std.Rco Int64} {op : w.type → Option w.type} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s g, Split S s.dmem → (k₁ v s).AllEnv E g P₁ → J.W (toEv {} (k₂ v s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (o.rmw lock s p op k₁).AllEnv E g P₁) :
    J.W (toEv {} (o.rmw lock s p op k₂)) g := by
  cases o with
  | reg x =>
    unfold RegOrMem.rmw at h ⊢
    simp only [MachineData.setReg] at h ⊢
    cases hop : op (s.regs.get x) <;> simp only [hop] at h ⊢ <;> exact hk _ _ _ hs h
  | mem a =>
    unfold RegOrMem.rmw at h ⊢
    cases lock with
    | true => exact rmwK_jsim J hk hs h
    | false => exact rmwPlain_jsim J hk hs h

/-! ### Per instruction -/

theorem jW_ite (c : Prop) [Decidable c] (a b : EvTree MachineState) (g : E.State) :
    J.W (if c then a else b) g ↔ if c then J.W a g else J.W b g := by
  split <;> rfl

theorem allEnv_ite' (c : Prop) [Decidable c] (a b : Effects) (g : E.State) :
    (if c then a else b).AllEnv E g P₁ ↔ if c then a.AllEnv E g P₁ else b.AllEnv E g P₁ := by
  split <;> rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp MachineData.set
  MachineData.load MachineData.store MachineData.storeNT MachineData.rmwK MachineData.rmwPlain RegOrMem.rmw
  AvxRegOrMem.interp AvxOperand.interp MachineData.setAvx MachineData.setAvxLegacy
  MachineData.loadAvx MachineData.storeAvx MachineData.rmw16K MachineData.rmw16Plain

set_option hygiene false in
/-- `InvLinkX64.isim_search` with the laws of `J` in place of `AllInv`'s
equations (and `EnvSpikeA64.jsim_search`'s `fence`/`choose`/`fault` cases). -/
local macro "jsim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Reg.interp, MachineData.setReg, Effects.AllEnv, toEv, toEv_ite,
      jW_ite, allEnv_ite'] at h ⊢ <;>
    repeat' first
      | exact hk _ _ hs h
      | exact hj _ _ _ hs h
      | exact h.elim
      | exact J.fault
      | exact J.fence h.1 fun g' hg => hk _ _ hs (h.2 g' hg)
      | refine operand_jsim J (fun v s g hs h => ?_) (by assumption) h
      | refine regOrMem_jsim J (fun v s g hs h => ?_) (by assumption) h
      | refine relRegOrMem_jsim J (fun v s g hs h => ?_) (by assumption) h
      | refine set_jsim J (fun s g hs h => ?_) (by assumption) h
      | refine load_jsim J (fun v s g hs h => ?_) (by assumption) h
      | refine store_jsim J (fun s g hs h => ?_) (by assumption) h
      | refine storeNT_jsim J (fun s g hs h => ?_) (by assumption) h
      | refine rmwK_jsim J (fun v s g hs h => ?_) (by assumption) h
      | refine rmw_jsim J (fun v s g hs h => ?_) (by assumption) h
      | refine undefined_jsim J (fun v h => ?_) h
      | (refine J.choose fun i => ?_; specialize h (i.val == 1))
      | dsimp only at h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [Reg.interp, MachineData.setReg, Effects.AllEnv, toEv, toEv_ite, jW_ite,
          allEnv_ite'] at h ⊢))

set_option maxHeartbeats 1000000 in
theorem operation_jsim [Labels] [AddressSize] {w : Width} (op : Operation w) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, Split S s.dmem → (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (Operation.interp op p s k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (Operation.interp op p s k₂ j₂)) g := by
  cases op
  case xadd lock dst src => cases dst <;> jsim_search
  case bswap dst => cases w <;> jsim_search
  -- `movfs` is `mov` at a segment-relative address: unfold the segment forms.
  case movfs dst src =>
    rcases src with (_ | a) | v <;> rcases dst with _ | b <;>
      simp only [Operation.interp, Operand.interpSeg, RegOrMem.interpSeg, MachineData.setSeg] at h ⊢ <;>
      repeat' first
        | exact hk _ _ hs h
        | refine load_jsim J (fun v s g hs h => ?_) (by assumption) h
        | refine store_jsim J (fun s g hs h => ?_) (by assumption) h
        | simp only [MachineData.setSeg] at h ⊢
  -- `cmpfs` is `cmp` at a segment-relative address: unfold the segment forms.
  case cmpfs x y =>
    rcases y with (_ | b) | v <;> rcases x with _ | a <;>
      simp only [Operation.interp, Operand.interpSeg, RegOrMem.interpSeg, MachineData.setSeg] at h ⊢ <;>
      repeat' first
        | exact hk _ _ hs h
        | refine load_jsim J (fun v s g hs h => ?_) (by assumption) h
        | refine store_jsim J (fun s g hs h => ?_) (by assumption) h
        | simp only [MachineData.setSeg] at h ⊢
  all_goals jsim_search

set_option hygiene false in
/-- `jsim_search` for the vector operations. -/
local macro "avx_jsim_search" : tactic =>
  `(tactic| (
    simp only [AvxOperation.interp, MachineData.setAvxReg, Effects.AllEnv, toEv] at h ⊢ <;>
    repeat' first
      | exact hk _ _ hs h
      | exact h.elim
      | exact J.fault
      | refine avxOperand_jsim J hF hS (fun v s g hs h => ?_) (by assumption) h
      | refine avxRegOrMem_jsim J hF hS (fun v s g hs h => ?_) (by assumption) h
      | refine setAvx_jsim J hF hS (fun s g hs h => ?_) (by assumption) h
      | refine setAvxLegacy_jsim J hF hS (fun s g hs h => ?_) (by assumption) h
      | refine rmw16K_jsim J (fun v s g hs h => ?_) (by assumption) h
      | refine rmw16Plain_jsim J hF hS (fun v s g hs h => ?_) (by assumption) h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setAvxReg, Effects.AllEnv, toEv] at h ⊢))

include hF in
theorem avxOperation_jsim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w)
    (p : Std.Rco Int64) {s : MachineData} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (AvxOperation.interp op p s k₁).AllEnv E g P₁) :
    J.W (toEv {} (AvxOperation.interp op p s k₂)) g := by
  cases op <;> avx_jsim_search

include hF in
theorem instr_jsim (hS : Le16 S) [Labels] (i : Instr) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, Split S s.dmem → (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (i.interp s p k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (i.interp s p k₂ j₂)) g := by
  cases i with
  | regular asz osz op =>
    simp only [Instr.interp] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact operation_jsim J op p hk hj hs h
  | avx asz osz aop =>
    simp only [Instr.interp] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact avxOperation_jsim J hF hS aop p hk hs h

include hF in
theorem directive_jsim (hS : Le16 S) [Labels] (dir : Directive) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s g, Split S s.dmem → (k₁ s).AllEnv E g P₁ → J.W (toEv {} (k₂ s)) g)
    (hj : ∀ pc s g, Split S s.dmem → (j₁ pc s).AllEnv E g P₁ → J.W (toEv {} (j₂ pc s)) g)
    (hs : Split S s.dmem) {g : E.State} (h : (dir.interp s p k₁ j₁).AllEnv E g P₁) :
    J.W (toEv {} (dir.interp s p k₂ j₂)) g := by
  cases dir with
  | instr i => exact instr_jsim J hF hS i p hk hj hs h
  | label l => exact hk _ _ hs h
  | byteArray b => exact h.elim

end JSim

/-! ## One instruction -/

/-- **One instruction, any tree judgment, x64**
(`EnvSpikeA64.exec_treeJ_of_instrStepEnv` for x64; `InvLinkX64.
exec_allInv_of_instrStepEnv` for any `TreeJ`): at a thread state whose code
is `e`, with no declarations and a private memory split from `S`, an
environment step of `E` (fitting `S`, `Le16 S`) makes the thread's tree
satisfy `J`, provided the step's post-set gives `J.Post` at the state moved
to every new machine state whose private memory is still split. -/
theorem exec_treeJ_of_instrStepEnv {E : SharedEnv} (J : TreeJ E State) {S : SharedEnv.Layout}
    (hF : X64Fit S E) (hS : Le16 S)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {}) (hs : Split S st.st.1.dmem)
    (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → Split S m.1.dmem → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  obtain ⟨d, sz, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hstep hR hs ⊢
  subst he hds
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false] at htree
  split at htree
  · cases htree
  · cases htree
    let J' := J.comap (fun ms : MachineState => ({ exe, endPc, st := ms, showPc, decls := {} } : State))
    show J'.W _ g
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    unfold Kraken.Executable.stepAtEnv at hstep
    generalize pc + Int64.ofNat sz = pc' at hstep ⊢
    rcases hstep with hstep | hstep
    · refine directive_jsim J' hF hS d _ ?_ ?_ hs hstep
      · intro s' g' hs' h
        exact J'.done (hR _ _ h hs')
      · intro _ _ _ _ h
        exact h.elim
    · refine directive_jsim J' hF hS d _ ?_ ?_ hs hstep
      · intro _ _ _ h
        exact h.elim
      · intro pc s' g' hs' h
        exact J'.done (hR _ _ h hs')

/-- **One instruction, any live tree judgment, x64**: `exec_treeJ_of_instrStepEnv`
at `J.toTreeJ`; every x64 tree is live (`exec_rmwLive`), so there is no
static check. -/
theorem exec_treeJLive_of_instrStepEnv {E : SharedEnv} (J : SLR.EnvG.TreeJLive E State) {S : SharedEnv.Layout}
    (hF : X64Fit S E) (hS : Le16 S)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {}) (hs : Split S st.st.1.dmem)
    (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → Split S m.1.dmem → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := fun tree ht =>
  exec_treeJ_of_instrStepEnv J.toTreeJ hF hS he hds hs h hR tree ht (exec_rmwLive st tree ht)

/-- A live tree judgment of `E` is one of `E` restricted to `S`. -/
def _root_.Kraken.Promising.SLR.EnvG.TreeJLive.toWithin {E : SharedEnv} {σ : Type} (J : SLR.EnvG.TreeJLive E σ)
    (S : SharedEnv.Layout) : SLR.EnvG.TreeJLive (E.within S) σ where
  W := J.W
  Post := J.Post
  done := J.done
  fault := J.fault
  choose := J.choose
  load h₁ h₂ := J.load h₁.1 h₂
  store h₁ h₂ := J.store h₁.1 h₂
  rmw h₁ h₂ := J.rmw h₁.1 h₂
  fence h₁ h₂ := J.fence h₁.1 h₂

/-- **One instruction of `E.within S`, a live judgment of `E`** (the form of
the x64 rule link): `exec_treeJLive_of_instrStepEnv` at `J.toWithin S`. -/
theorem exec_treeJLive_of_instrStepEnvW {E : SharedEnv} (J : SLR.EnvG.TreeJLive E State) {S : SharedEnv.Layout}
    (hS : Le16 S)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {}) (hs : Split S st.st.1.dmem)
    (h : e.instrStepEnv (E.within S) (st.st, g) R)
    (hR : ∀ m g', R (m, g') → Split S m.1.dmem → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g :=
  exec_treeJLive_of_instrStepEnv (J.toWithin S) (within_fit E S) hS he hds hs h hR

end EnvG

end Kraken.Promising.X64
