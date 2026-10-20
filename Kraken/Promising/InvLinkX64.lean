/-
The invariant environment and the full Promising machine, x64 (design note
`Kraken/Promising/EnvWP.md`, "Invariant environment").

The x64 sibling of `InvLinkAArch64.lean`; the statements are the same, with
two extra side conditions, both about vector accesses:

- `Split S d`: no byte of a shared location is mapped in the thread's private
  memory `d`. The adapter's non-atomic vector accesses are *mapped-first per
  8-byte piece* (`loadPieces`/`storePieces`), while `AllEnv` sends every piece
  of an unmapped access to the environment; under `Split` the two agree (a
  piece the environment answers is a shared location, hence unmapped). It is
  part of `ThreadSpec.Holds` (instructions keep it: they only write `dmem`
  where it is mapped); `Split.of_get` discharges it from finitely many byte
  lookups, `Split.empty` for an empty `dmem`.
- `Le16 S`: every shared location is at most 16 bytes, so a vector access
  tagged `atomic` that `AllEnv` answers whole is the 16-byte access the
  adapter makes one event (as `SharedLayout.WF.le16` in `EnvWPX64.lean`);
  decidable for a concrete `S`.
-/
import Kraken.Promising.EnvLinkTermX64
import Kraken.Promising.CertifyX64
import Kraken.Promising.InvLink
import Kraken.SharedEnvInv

open Kraken

namespace Kraken.Promising.X64

/-! ## Side conditions -/

/-- No byte of a shared location of `S` is mapped in the private memory `d`. -/
def Split (S : SharedEnv.Layout) (d : DataMem) : Prop :=
  ∀ k, SharedLayout.Covers S k → d.get? k = none

/-- Every shared location of `S` is at most 16 bytes wide. -/
def Le16 (S : SharedEnv.Layout) : Prop := ∀ x ∈ S, x.2 ≤ 16

instance (S : SharedEnv.Layout) : Decidable (Le16 S) := inferInstanceAs (Decidable (∀ x ∈ S, x.2 ≤ 16))

theorem Split.empty (S : SharedEnv.Layout) : Split S ∅ := fun _ _ => by simp

/-- `Split` from the bytes of each shared location (finitely many lookups). -/
theorem Split.of_get {S : SharedEnv.Layout} {d : DataMem}
    (h : ∀ a n, (a, n) ∈ S → ∀ i < n, d.get? (a + BitVec.ofNat 64 i) = none) : Split S d := by
  rintro k ⟨a, n, hmem, hlt⟩
  have := h a n hmem _ hlt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this

/-- A store where `d` is mapped keeps `Split`. -/
theorem Split.storeInt {S : SharedEnv.Layout} {d : DataMem} (h : Split S d) {a : BitVec 64} {n : Nat}
    (x : Int) (hd : (d.loadBytes a n).isSome) : Split S (Mem.storeInt d a n x) := by
  have hlen : (Int.toBytes n x).length = n := Int.toBytes_length n x
  intro k hk
  simp only [Mem.storeInt, Mem.get?_storeBytes, h k hk, Option.or_none]
  rw [Std.ExtHashMap.get?_eq_getElem?]
  refine Std.ExtHashMap.getElem?_eq_none fun hm => ?_
  rw [mem_At_iff, hlen] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  have := Mem.get?_isSome_of_loadBytes hd i hi
  rw [h _ hk] at this
  cases this

/-- Under `Split`, an 8-byte shared location is unmapped. -/
theorem Split.piece_none {S : SharedEnv.Layout} {d : DataMem} (h : Split S d) {a : BitVec 64}
    (hmem : (a, 8) ∈ S) : d.loadBytes a 8 = none := by
  cases hb : d.loadBytes a 8 with
  | none => rfl
  | some bs =>
    have := Mem.get?_isSome_of_loadBytes (m := d) (a := a) (n := 8) (by rw [hb]; rfl) 0 (by decide)
    rw [h _ (SharedLayout.covers_of_mem hmem (by decide) (by decide))] at this
    cases this

/-- Under `Split`, a shared location (of `1` to `16` bytes) does not load from
the private memory. -/
theorem Split.loadInt_none {S : SharedEnv.Layout} {d : DataMem} (h : Split S d) {a : BitVec 64} {n : Nat}
    (hmem : (a, n) ∈ S) (hpos : 0 < n) (hle : n ≤ 16) : Mem.loadInt d a n = none := by
  cases hl : Mem.loadInt d a n with
  | none => rfl
  | some x =>
    have := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 hpos
    rw [h _ (SharedLayout.covers_of_mem hmem hpos hle)] at this
    cases this

private theorem avx_bytes_eq' (w : AvxWidth) : w.bytes = 8 * (w.bytes / 8) := by cases w <;> rfl

private theorem w128_of_le16 {S : SharedEnv.Layout} (hS : Le16 S) {addr : BitVec 64} {w : AvxWidth}
    (h : (addr, w.bytes) ∈ S) : w = .W128 := by
  have := hS _ h
  cases w <;> simp_all [AvxWidth.bytes]

theorem pieceVal_toBytes (p : BitVec 64) : pieceVal (Int.toBytes 8 p.toInt) = p := by
  unfold pieceVal
  rw [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl, BitVec.ofInt_toInt]

/-! ## The simulation, per primitive -/

section ISim

variable {S : SharedEnv.Layout} {G : Loc → Val → Prop} {P₁ : MachineState → Unit → Prop}
  {Q : MachineState → Prop}

local notation "IE" => SharedEnv.inv S G

/-- The pieces of a non-atomic vector load: under `Split`, every piece
`LoadPieces` answers is unmapped, so the adapter makes each an event. -/
theorem loadPieces_isim {d : DataMem} (hs : Split S d) :
    ∀ (n : Nat) (addr : BitVec 64) (K : List (BitVec 64) → Unit → Prop) (k : List UInt8 → EvTree MachineState),
      (IE).LoadPieces addr n () K →
      (∀ vs : List (BitVec 128), K (vs.map (·.setWidth 64)) () → (k (piecesBytes vs)).AllInv G Q) →
      (loadPieces {} d addr n k).AllInv G Q
  | 0, _, _, _, h, hk => hk [] h
  | n + 1, addr, K, k, h, hk => by
    obtain ⟨hok, h⟩ := h
    have hmem : (addr, 8) ∈ S := hok
    unfold loadPieces
    rw [hs.piece_none hmem]
    simp only
    split
    · trivial
    · simp only [EvTree.access_empty, EvTree.AllInv]
      intro v hv
      exact loadPieces_isim hs n (addr + 8) _ _ (h v () hv) fun vs hK => hk (v :: vs) hK

/-- The pieces of a non-atomic vector store: under `Split`, every piece is an
event, and the private memory is unchanged. -/
theorem storePieces_isim {d : DataMem} (hs : Split S d) :
    ∀ (ps : List (BitVec 64)) (addr : BitVec 64) (K : Unit → Prop) (k : DataMem → EvTree MachineState),
      (IE).StorePieces addr ps () K → (K () → (k d).AllInv G Q) →
      (storePieces {} addr ps.length (ps.flatMap fun p => Int.toBytes 8 p.toInt) d k).AllInv G Q
  | [], _, _, _, h, hk => hk h
  | p :: ps, addr, K, k, h, hk => by
    obtain ⟨⟨hmem, hG⟩, h⟩ := h
    simp only [List.length_cons]
    unfold storePieces
    rw [hs.piece_none hmem]
    simp only
    split
    · trivial
    · have htake : (List.flatMap (fun p => Int.toBytes 8 p.toInt) (p :: ps)).take 8 = Int.toBytes 8 p.toInt := by
        rw [List.flatMap_cons, List.take_left' (Int.toBytes_length 8 _)]
      have hdrop : (List.flatMap (fun p => Int.toBytes 8 p.toInt) (p :: ps)).drop 8 =
          ps.flatMap fun p => Int.toBytes 8 p.toInt := by
        rw [List.flatMap_cons, List.drop_left' (Int.toBytes_length 8 _)]
      simp only [EvTree.access_empty, EvTree.AllInv, htake, hdrop, pieceVal_toBytes]
      exact ⟨hG, fun _ _ => storePieces_isim hs ps (addr + 8) K k (h true () (.inl rfl)) hk⟩

/-- `undefined`: a Boolean is a `choose` of the adapter; any other kind of
value is a fault, about which `AllInv` says nothing. -/
theorem undefined_isim {α : Type} {inst : NondetSupportingType α} {ret₁ ret₂ : α → Effects}
    (hk : ∀ v, (ret₁ v).AllEnv IE () P₁ → (toEv {} (ret₂ v)).AllInv G Q)
    (h : ∀ v, (ret₁ v).AllEnv IE () P₁) : (toEv {} (Effects.undefined ret₂)).AllInv G Q := by
  cases inst <;> simp only [toEv, EvTree.AllInv]
  exact fun i => hk _ (h _)

theorem load_isim {s : MachineData} {addr : BitVec 64} {w : Width} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.load s addr w k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.load s addr w k₂)).AllInv G Q := by
  unfold MachineData.load at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ _ hs h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact fun v hv => hk _ _ hs (h.2 v () hv)

theorem store_isim {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.store s addr v k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.store s addr v k₂)).AllInv G Q := by
  unfold MachineData.store at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact ⟨h.1.2, fun b _ => hk _ hs (h.2 true () (.inl rfl))⟩

theorem storeNT_isim {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.storeNT s addr v k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.storeNT s addr v k₂)).AllInv G Q := by
  unfold MachineData.storeNT at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => rw [hd] at h; exact hk _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact ⟨h.1.2, fun b hb => hk _ hs (h.2 b () hb)⟩

theorem rmwK_isim {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.rmwK s rk addr w op k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.rmwK s rk addr w op k₂)).AllInv G Q := by
  unfold MachineData.rmwK at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt w.bits x) <;> rw [hop] at h
    · exact hk _ _ hs h
    · exact hk _ _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact fun old hold => ⟨fun v hv => h.1.2 old hold v hv, hk _ _ hs (h.2 old () hold)⟩

theorem rmwPlain_isim {s : MachineData} {addr : BitVec 64} {w : Width} {op : w.type → Option w.type}
    {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.rmwPlain s addr w op k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.rmwPlain s addr w op k₂)).AllInv G Q := by
  unfold MachineData.rmwPlain at h ⊢
  refine load_isim (fun v s hs h => ?_) hs h
  cases hop : op v with
  | some new =>
    simp only [hop] at h ⊢
    exact store_isim (fun s hs h => hk _ _ hs h) hs h
  | none =>
    simp only [hop] at h ⊢
    exact hk _ _ hs h

theorem loadAvx_isim (hS : Le16 S) {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {k₁ k₂ : w.type → MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.loadAvx s addr w k₁ checkAlign atomic).AllEnv IE () P₁) :
    (toEv {} (MachineData.loadAvx s addr w k₂ checkAlign atomic)).AllInv G Q := by
  unfold MachineData.loadAvx at h ⊢
  split
  · simp only [toEv, EvTree.AllInv]
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllEnv, toEv] at h ⊢
    cases hd : Mem.loadInt s.dmem addr w.bytes with
    | some x => rw [hd] at h; exact hk _ _ hs h
    | none =>
      rw [hd] at h
      cases atomic with
      | true =>
        simp only [Effects.AllEnv] at h
        obtain ⟨hok, h⟩ := h
        have hmem : (addr, w.bytes) ∈ S := hok
        obtain rfl := w128_of_le16 hS hmem
        simp only [toEv, Bool.true_and, EvTree.access_empty]
        exact fun v hv => hk _ _ hs (h v () hv)
      | false =>
        simp only [Effects.AllEnv] at h
        simp only [toEv, Bool.false_and, Bool.false_eq_true, ite_false]
        refine loadPieces_isim hs _ addr _ _ h fun vs hK => ?_
        rw [ofInt_ofBytes_piecesBytes]
        exact hk _ _ hs hK

theorem storeAvx_isim (hS : Le16 S) {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type}
    {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.storeAvx s addr v k₁ checkAlign atomic).AllEnv IE () P₁) :
    (toEv {} (MachineData.storeAvx s addr v k₂ checkAlign atomic)).AllInv G Q := by
  unfold MachineData.storeAvx at h ⊢
  split
  · simp only [toEv, EvTree.AllInv]
  · rename_i hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    simp only [Effects.AllEnv, toEv] at h ⊢
    cases hd : Mem.loadInt s.dmem addr w.bytes with
    | some x => rw [hd] at h; exact hk _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
    | none =>
      rw [hd] at h
      cases atomic with
      | true =>
        simp only [Effects.AllEnv] at h
        obtain ⟨⟨hmem, hG⟩, h⟩ := h
        obtain rfl := w128_of_le16 hS hmem
        simp only [toEv, Bool.true_and, EvTree.access_empty]
        exact ⟨hG, fun _ _ => hk _ hs (h true () (.inl rfl))⟩
      | false =>
        simp only [Effects.AllEnv] at h
        simp only [toEv, Bool.false_and, Bool.false_eq_true, ite_false]
        have hb : Int.toBytes w.bytes v.toInt = (toPieces v (w.bytes / 8)).flatMap fun p => Int.toBytes 8 p.toInt := by
          rw [← toBytes_toPieces (by cases w <;> rfl) v, ← avx_bytes_eq' w]
        rw [hb]
        have hl := length_toPieces v (w.bytes / 8)
        have := storePieces_isim (Q := Q) hs (toPieces v (w.bytes / 8)) addr _ (fun d => toEv {} (k₂ { s with dmem := d }))
          h (fun hK => hk _ hs hK)
        rwa [hl] at this

theorem rmw16K_isim {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {k₁ k₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.rmw16K s rk addr op k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.rmw16K s rk addr op k₂)).AllInv G Q := by
  unfold MachineData.rmw16K at h ⊢
  simp only [Effects.AllEnv, toEv] at h ⊢
  cases hd : Mem.loadInt s.dmem addr 16 with
  | some x =>
    rw [hd] at h
    simp only at h ⊢
    cases hop : op (BitVec.ofInt 128 x) <;> rw [hop] at h
    · exact hk _ _ hs h
    · exact hk _ _ (hs.storeInt _ (Mem.loadBytes_isSome_of_loadInt hd)) h
  | none =>
    rw [hd] at h
    simp only [Effects.AllEnv, toEv, EvTree.access_empty, EvTree.AllInv] at h ⊢
    exact fun old hold => ⟨fun v hv => h.1.2 old hold v hv, hk _ _ hs (h.2 old () hold)⟩

theorem rmw16Plain_isim (hS : Le16 S) {s : MachineData} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {k₁ k₂ : BitVec 128 → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.rmw16Plain s addr op k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.rmw16Plain s addr op k₂)).AllInv G Q := by
  unfold MachineData.rmw16Plain at h ⊢
  refine loadAvx_isim hS (fun v s hs h => ?_) hs h
  cases hop : op v with
  | some new =>
    simp only [hop] at h ⊢
    exact storeAvx_isim hS (fun s hs h => hk _ _ hs h) hs h
  | none =>
    simp only [hop] at h ⊢
    exact hk _ _ hs h

/-! ### Operands -/

theorem avxRegOrMem_isim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {o : AvxRegOrMem w}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (o.interp s p k₁ checkAlign atomic).AllEnv IE () P₁) :
    (toEv {} (o.interp s p k₂ checkAlign atomic)).AllInv G Q := by
  cases o with
  | avx x => exact hk _ _ hs h
  | mem a => exact loadAvx_isim hS hk hs h

theorem avxOperand_isim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {o : AvxOperand w}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects} {checkAlign : Bool}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (o.interp s p k₁ checkAlign).AllEnv IE () P₁) :
    (toEv {} (o.interp s p k₂ checkAlign)).AllInv G Q := by
  cases o with
  | regOrMem rm => exact avxRegOrMem_isim hS hk hs h

theorem setAvx_isim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.setAvx s dst v p k₁ checkAlign atomic).AllEnv IE () P₁) :
    (toEv {} (MachineData.setAvx s dst v p k₂ checkAlign atomic)).AllInv G Q := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvx, MachineData.setAvxReg] at h ⊢
    exact hk _ hs h
  | mem a => exact storeAvx_isim hS hk hs h

theorem setAvxLegacy_isim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} {dst : AvxDst w} {v : w.type}
    {p : Std.Rco Int64} {s : MachineData} {k₁ k₂ : MachineData → Effects} {checkAlign atomic : Bool}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.setAvxLegacy s dst v p k₁ checkAlign atomic).AllEnv IE () P₁) :
    (toEv {} (MachineData.setAvxLegacy s dst v p k₂ checkAlign atomic)).AllInv G Q := by
  cases dst with
  | avx x =>
    simp only [MachineData.setAvxLegacy, MachineData.setAvxLegacyReg] at h ⊢
    exact hk _ hs h
  | mem a => exact storeAvx_isim hS hk hs h

theorem regOrMem_isim [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (o.interp s p k₁).AllEnv IE () P₁) : (toEv {} (o.interp s p k₂)).AllInv G Q := by
  cases o with
  | reg x => exact hk _ _ hs h
  | mem a => exact load_isim hk hs h

theorem operand_isim [Labels] [AddressSize] {w : Width} {o : Operand w} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (o.interp s p k₁).AllEnv IE () P₁) : (toEv {} (o.interp s p k₂)).AllInv G Q := by
  cases o with
  | regOrMem rm => exact regOrMem_isim hk hs h
  | imm v => exact hk _ _ hs h

theorem relRegOrMem_isim [Labels] [AddressSize] {o : RelRegOrMem} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : BitVec 64 → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (o.interp s p k₁).AllEnv IE () P₁) : (toEv {} (o.interp s p k₂)).AllInv G Q := by
  cases o with
  | rel c => exact hk _ _ hs h
  | reg x => exact hk _ _ hs h
  | mem a => exact load_isim hk hs h

theorem set_isim [Labels] [AddressSize] {w : Width} {dst : Dst w} {v : w.type} {p : Std.Rco Int64}
    {s : MachineData} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (MachineData.set s dst v p k₁).AllEnv IE () P₁) :
    (toEv {} (MachineData.set s dst v p k₂)).AllInv G Q := by
  cases dst with
  | reg x =>
    simp only [MachineData.set, MachineData.setReg] at h ⊢
    exact hk _ hs h
  | mem a => exact store_isim hk hs h

theorem rmw_isim [Labels] [AddressSize] {w : Width} {o : RegOrMem w} {lock : Bool}
    {p : Std.Rco Int64} {op : w.type → Option w.type} {s : MachineData} {k₁ k₂ : w.type → MachineData → Effects}
    (hk : ∀ v s, Split S s.dmem → (k₁ v s).AllEnv IE () P₁ → (toEv {} (k₂ v s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (o.rmw lock s p op k₁).AllEnv IE () P₁) :
    (toEv {} (o.rmw lock s p op k₂)).AllInv G Q := by
  cases o with
  | reg x =>
    unfold RegOrMem.rmw at h ⊢
    simp only [MachineData.setReg] at h ⊢
    cases hop : op (s.regs.get x) <;> simp only [hop] at h ⊢ <;> exact hk _ _ hs h
  | mem a =>
    unfold RegOrMem.rmw at h ⊢
    cases lock with
    | true => exact rmwK_isim hk hs h
    | false => exact rmwPlain_isim hk hs h

/-! ### Per instruction -/

theorem toEv_ite (ds : Decls) (c : Prop) [Decidable c] (a b : Effects) :
    toEv ds (if c then a else b) = if c then toEv ds a else toEv ds b := by
  split <;> rfl

theorem allInv_ite (c : Prop) [Decidable c] (a b : EvTree MachineState) :
    (if c then a else b).AllInv G Q ↔ if c then a.AllInv G Q else b.AllInv G Q := by
  split <;> rfl

theorem allEnv_ite (c : Prop) [Decidable c] (a b : Effects) :
    (if c then a else b).AllEnv IE () P₁ ↔ if c then a.AllEnv IE () P₁ else b.AllEnv IE () P₁ := by
  split <;> rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp MachineData.set
  MachineData.load MachineData.store MachineData.storeNT MachineData.rmwK MachineData.rmwPlain RegOrMem.rmw
  AvxRegOrMem.interp AvxOperand.interp MachineData.setAvx MachineData.setAvxLegacy
  MachineData.loadAvx MachineData.storeAvx MachineData.rmw16K MachineData.rmw16Plain

set_option hygiene false in
/-- Reduce the interpreter on both sides and apply the dictionary until the
continuation hypotheses `hk`/`hj` close every leaf. -/
local macro "isim_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Reg.interp, MachineData.setReg, Effects.AllEnv, toEv, EvTree.AllInv, SharedEnv.inv_ok_fence,
      SharedEnv.inv_step_fence, true_and, forall_const, toEv_ite, allInv_ite, allEnv_ite] at h ⊢ <;>
    repeat' first
      | exact hk _ hs h
      | exact hj _ _ hs h
      | exact h.elim
      | exact hk _ hs (h () trivial)
      | exact hk _ hs (h.2 () trivial)
      | refine operand_isim (fun v s hs h => ?_) hs h
      | refine regOrMem_isim (fun v s hs h => ?_) hs h
      | refine relRegOrMem_isim (fun v s hs h => ?_) hs h
      | refine set_isim (fun s hs h => ?_) hs h
      | refine load_isim (fun v s hs h => ?_) hs h
      | refine store_isim (fun s hs h => ?_) hs h
      | refine storeNT_isim (fun s hs h => ?_) hs h
      | refine rmwK_isim (fun v s hs h => ?_) hs h
      | refine rmw_isim (fun v s hs h => ?_) hs h
      | refine undefined_isim (fun v h => ?_) h
      | (refine fun v => ?_; specialize h v)
      | dsimp only at h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [Reg.interp, MachineData.setReg, Effects.AllEnv, toEv, EvTree.AllInv, SharedEnv.inv_ok_fence, SharedEnv.inv_step_fence, true_and,
          forall_const, toEv_ite, allInv_ite, allEnv_ite] at h ⊢))

set_option maxHeartbeats 1000000 in
theorem operation_isim [Labels] [AddressSize] {w : Width} (op : Operation w) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hj : ∀ pc s, Split S s.dmem → (j₁ pc s).AllEnv IE () P₁ → (toEv {} (j₂ pc s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (Operation.interp op p s k₁ j₁).AllEnv IE () P₁) :
    (toEv {} (Operation.interp op p s k₂ j₂)).AllInv G Q := by
  cases op
  case xadd lock dst src => cases dst <;> isim_search
  case bswap dst => cases w <;> isim_search
  all_goals isim_search

set_option hygiene false in
/-- `isim_search` for the vector operations. -/
local macro "avx_isim_search" : tactic =>
  `(tactic| (
    simp only [AvxOperation.interp, MachineData.setAvxReg, Effects.AllEnv, toEv, EvTree.AllInv] at h ⊢ <;>
    repeat' first
      | exact hk _ hs h
      | exact h.elim
      | refine avxOperand_isim hS (fun v s hs h => ?_) hs h
      | refine avxRegOrMem_isim hS (fun v s hs h => ?_) hs h
      | refine setAvx_isim hS (fun s hs h => ?_) hs h
      | refine setAvxLegacy_isim hS (fun s hs h => ?_) hs h
      | refine rmw16K_isim (fun v s hs h => ?_) hs h
      | refine rmw16Plain_isim hS (fun v s hs h => ?_) hs h
      | (split <;> rename_i hcond <;>
          simp only [hcond, ite_true, ite_false, Bool.false_eq_true] at h ⊢)
      | simp only [MachineData.setAvxReg, Effects.AllEnv, toEv, EvTree.AllInv] at h ⊢))

theorem avxOperation_isim (hS : Le16 S) [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w)
    (p : Std.Rco Int64) {s : MachineData} {k₁ k₂ : MachineData → Effects}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (AvxOperation.interp op p s k₁).AllEnv IE () P₁) :
    (toEv {} (AvxOperation.interp op p s k₂)).AllInv G Q := by
  cases op <;> avx_isim_search

theorem instr_isim (hS : Le16 S) [Labels] (i : Instr) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hj : ∀ pc s, Split S s.dmem → (j₁ pc s).AllEnv IE () P₁ → (toEv {} (j₂ pc s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (i.interp s p k₁ j₁).AllEnv IE () P₁) :
    (toEv {} (i.interp s p k₂ j₂)).AllInv G Q := by
  cases i with
  | regular asz osz op =>
    simp only [Instr.interp] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact operation_isim op p hk hj hs h
  | avx asz osz aop =>
    simp only [Instr.interp] at h ⊢
    generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
    exact avxOperation_isim hS aop p hk hs h

theorem directive_isim (hS : Le16 S) [Labels] (dir : Directive) (p : Std.Rco Int64)
    {s : MachineData} {k₁ k₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hk : ∀ s, Split S s.dmem → (k₁ s).AllEnv IE () P₁ → (toEv {} (k₂ s)).AllInv G Q)
    (hj : ∀ pc s, Split S s.dmem → (j₁ pc s).AllEnv IE () P₁ → (toEv {} (j₂ pc s)).AllInv G Q)
    (hs : Split S s.dmem) (h : (dir.interp s p k₁ j₁).AllEnv IE () P₁) :
    (toEv {} (dir.interp s p k₂ j₂)).AllInv G Q := by
  cases dir with
  | instr i => exact instr_isim hS i p hk hj hs h
  | label l => exact hk _ hs h
  | byteArray b => exact h.elim

end ISim

/-! ## Instruction steps -/

/-- **One instruction.** At a thread state whose code is `e` (validly laid
out), with no declarations and a private memory split from `S`, an
environment step of `inv S G` from the thread's machine state makes the
thread's instruction tree satisfy `AllInv G`, with every leaf in the step's
post-set, still split (and the code, end address and declarations
unchanged). -/
theorem exec_allInv_of_instrStepEnv {S : SharedEnv.Layout} {G : Loc → Val → Prop} (hS : Le16 S)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    {R : MachineState × Unit → Prop} (he : st.exe = e) (hds : st.decls = {}) (hs : Split S st.st.1.dmem)
    (h : e.instrStepEnv (SharedEnv.inv S G) (st.st, ()) R) :
    ∀ tree, isa.exec st = some tree →
      tree.AllInv G (fun st' : State => (R (st'.st, ()) ∧ Split S st'.st.1.dmem) ∧ st'.exe = st.exe ∧
        st'.endPc = st.endPc ∧ st'.decls = st.decls) := by
  intro tree htree
  obtain ⟨d, sz, rest, hcode, hstep⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hstep hs ⊢
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
    rw [EvTree.allInv_map]
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    unfold Kraken.Executable.stepAtEnv at hstep
    generalize pc + Int64.ofNat sz = pc' at hstep ⊢
    rcases hstep with hstep | hstep
    · refine directive_isim hS d _ ?_ ?_ hs hstep
      · intro s' hs' h
        exact ⟨⟨h, hs'⟩, trivial, trivial, trivial⟩
      · intro _ _ _ h
        exact h.elim
    · refine directive_isim hS d _ ?_ ?_ hs hstep
      · intro _ _ h
        exact h.elim
      · intro pc s' hs' h
        exact ⟨⟨h, hs'⟩, trivial, trivial, trivial⟩

/-! ## Thread specifications -/

/-- What a thread's proof in `inv S G` provides: its code (validly laid
out), end address, postcondition (only at the end address) and an inductive
invariant of the environment step relation: every invariant state satisfies
the postcondition or takes an environment step into invariant states. A
`Safely` judgment is one (`ofSafely`; `TripleEnv`/`cfgEnv` conclusions give
`Eventually`, hence `Safely`). -/
structure ThreadSpec (S : SharedEnv.Layout) (G : Loc → Val → Prop) where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  inv : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc
  closed : ∀ y, inv y → post y ∨ ∃ R, e.instrStepEnv (SharedEnv.inv S G) y R ∧ ∀ z, R z → inv z

/-- The specification from a `Safely` judgment (its invariant is `Safely`
itself). -/
def ThreadSpec.ofSafely {S : SharedEnv.Layout} {G : Loc → Val → Prop} (e : Kraken.Executable Directive)
    [hv : Kraken.Executable.ValidLayout e] (endPc : Int64) (P : MachineState × Unit → Prop)
    (hPend : ∀ y, P y → y.1.2 = endPc) : ThreadSpec S G where
  e := e
  valid := hv
  endPc := endPc
  post := P
  inv := Safely (e.instrStepEnv (SharedEnv.inv S G)) P
  post_end := hPend
  closed := fun _ h => h.unfold

/-- The specification holds at a thread state of the Promising machine: its
code, end address, no declarations, a private memory split from `S`, and the
invariant at its machine state. -/
def ThreadSpec.Holds {S : SharedEnv.Layout} {G : Loc → Val → Prop} (sp : ThreadSpec S G) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧ Split S st.st.1.dmem ∧ sp.inv (st.st, ())

/-- The specification of a program `p` proved by a `TripleEnv` in `inv S G`
with no exceptional exit: postcondition `Q` at the end of the text. -/
def ThreadSpec.ofTripleEnv {S : SharedEnv.Layout} {G : Loc → Val → Prop} [layout : _root_.Layout]
    (p : Program) [Kraken.Executable.ValidLayout (layout p)] (Q : MachineData → Unit → Prop) :
    ThreadSpec S G :=
  ThreadSpec.ofSafely (layout p) ((layout p).addrOf p.length)
    (fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False)
    (fun _ h => h.elim And.left False.elim)

/-- A thread state at the start of `p`'s text, whose machine state satisfies
the `TripleEnv`'s precondition and a private memory split from `S`, satisfies `ofTripleEnv`. -/
theorem ThreadSpec.ofTripleEnv_holds {S : SharedEnv.Layout} {G : Loc → Val → Prop} [CodeEnv]
    [layout : _root_.Layout] {p : Program} [Kraken.Executable.ValidLayout (layout p)]
    {P Q : MachineData → Unit → Prop}
    (ht : MachineWP.TripleEnv (SharedEnv.inv S G) P p Q (fun _ _ _ => False))
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p)
    (hend : st.endPc = (layout p).addrOf p.length) (hds : st.decls = {})
    (hpc : st.st.2 = Kraken.Layout.start Directive) (hP : P st.st.1 ())
    (hs : Split S st.st.1.dmem) :
    (ThreadSpec.ofTripleEnv (S := S) (G := G) p Q).Holds st := by
  refine ⟨he, hend, hds, hs, ?_⟩
  have hev := Program.instrStepEnv_of_tripleEnv ht (s := st.st.1) (g := ()) hP henv
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := Prod.ext rfl hpc
  rw [hst]
  exact Safely.of_eventually hev

/-- A thread specification is kept by every instruction against a memory
satisfying `MemInv G`, which the instruction keeps too. -/
theorem threadSpec_stepPreserves {A : Arch} {S : SharedEnv.Layout} {G : Loc → Val → Prop} (hS : Le16 S)
    (sp : Nat → ThreadSpec S G) :
    StepPreserves (I := isa) A G (fun tid st => (sp tid).Holds st) := by
  intro tid t mem outs o ⟨he, hend, hds, hs, hinv⟩ hm hstep ho
  have hv := (sp tid).valid
  rcases (sp tid).closed _ hinv with hP | ⟨R, hT, hR⟩
  · -- at the end address: the thread has halted
    have hpc : t.st.st.2 = (sp tid).endPc := (sp tid).post_end _ hP
    unfold stepOne at hstep
    have hex : isa.exec t.st = none := by
      show exec t.st = none
      simp [exec, hpc, hend]
    rw [hex] at hstep
    cases hstep
  · obtain ⟨⟨⟨hRo, hs'⟩, he', hend', hds'⟩, hm'⟩ :=
      stepOne_allInv A hstep ho (fun tree htree => exec_allInv_of_instrStepEnv hS he hds hs hT tree htree) hm
    exact ⟨⟨he'.trans he, hend'.trans hend, hds'.trans hds, hs', hR _ hRo⟩, hm'⟩

/-! ## The links -/

/-- **Links A and B.** If every shared location is at most 16 bytes, the
memory of `c0` satisfies `MemInv G` and every thread `tid` of `c0` satisfies
its specification `sp tid` (a proof in `inv S G` of its own program, from a
private memory split from `S`), then at every configuration reachable from
`c0` on the full machine (any number of threads, promises included) the
memory satisfies `MemInv G` and every thread still satisfies its
specification, in particular its invariant. -/
theorem inv_reachable {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop} (hS : Le16 S)
    (sp : Nat → ThreadSpec S G) {c0 c : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).Holds t.st) (h : Reachable A fuel c0 c) :
    MemInv G c.mem ∧ ∀ tid t, c.threads[tid]? = some t → (sp tid).Holds t.st :=
  configInv_reachable (threadSpec_stepPreserves hS sp) ⟨hm0, h0⟩ h

/-- **Link A, through `write_invariant`**: the specifications discharge its
premise `WritesPreserve`. -/
theorem inv_writesPreserve {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (hS : Le16 S) (sp : Nat → ThreadSpec S G) {c0 : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).Holds t.st) : WritesPreserve A fuel G c0 :=
  writesPreserve_of_stepPreserves (threadSpec_stepPreserves hS sp) ⟨hm0, h0⟩

/-- **Link B at the end address**: in every reachable configuration, a thread
at its end address (where its code has no environment step, `hstuck`)
satisfies its postcondition. -/
theorem inv_reachable_post {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (hS : Le16 S) (sp : Nat → ThreadSpec S G) {c0 c : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).Holds t.st) (h : Reachable A fuel c0 c)
    {tid : Nat} {t : Thread isa} (ht : c.threads[tid]? = some t)
    (hstuck : ∀ x R, x.1.2 = (sp tid).endPc → ¬ (sp tid).e.instrStepEnv (SharedEnv.inv S G) x R)
    (hend : t.st.st.2 = (sp tid).endPc) : (sp tid).post (t.st.st, ()) := by
  obtain ⟨-, -, -, -, hinv⟩ := (inv_reachable hS sp hm0 h0 h).2 tid t ht
  rcases (sp tid).closed _ hinv with hP | ⟨R, hT, -⟩
  · exact hP
  · exact (hstuck _ R hend hT).elim

end Kraken.Promising.X64
