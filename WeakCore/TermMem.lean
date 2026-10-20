/-
T3c-3b: the memory invariant.

Σ (`TEnv.sto`, T3c-3) says what each cell holds; this file says what memory
holds, as the promise machine sees it (`TermRun`, `Promises`).

* `ValOf η T vs`: the values `vs` are a value of the closed type `T` (`VR` in
  the variable-free view `CE η`), validly encoded (`Valid`, T3c-4c).
* `MemOK η mem pairs`: every message at a cell of Σ is the allocation's `undef`
  placeholder or **word `o` of some value** of the cell's type (semantic tear,
  per word); the two messages of a pair store are two words of
  **one** value (single-copy atomicity of a `.two` unit); pair timestamps are
  in memory.
* `OwnOK η mem vs`: for each of the thread's own cells, its coherence view is at
  the last message of every word, and those messages form a value, as many
  words as the cell type's word count `wc` (T3c-4c: not its access list
  `accs`, which a runtime rendition of the type need not share; `wc`, `shp`
  and `Valid` are functions of `sig`).  So a load
  of an own cell can read only that message (`readable_latest`), and a load
  changes no coherence there (`stepLoad_latest`).

What is not here yet: Σ-locality for `pub` cells (T3c-4/5, with the loads), and
promises (other threads' promises to own cells are excluded by certification,
T3c-7).

Build: LEAN_PATH=build lean TermMem.lean
-/
import WeakCore.TermSound
import WeakCore.TermTear

namespace TermMem
open CoreLang CoreTerm TermRun TermClose TermSound
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Values of a cell, and the invariant -/

/-- The values `vs` are a value of the closed type `T`, read in `η`'s global
view (no type variables; Σ, program and thread are `η`'s), and validly encoded
at `T` (`Valid`; T3c-4c, so a load can hand back a `Lay`). -/
def ValOf (η : TEnv) (T : Ty) (ws : List Word) : Prop :=
  VR (fun _ => 0) (CE η.unsee) T (shp T) ws ∧ Valid T ws

/-- (D3) A value held in the thread's view (its `seen` labels included): what
a store writes, before its message views are taken into account. -/
def EnvVal (η : TEnv) (T : Ty) (ws : List Word) : Prop :=
  VR (fun _ => 0) (CE η) T (shp T) ws ∧ Valid T ws

/-- (D3) Every label `η` has `seen` is published at a frontier at most `V`. -/
def SeenLE (η : TEnv) (V : Ts) : Prop :=
  ∀ l, η.seen l → ∃ f, η.pfr l = some f ∧ f ≤ V

theorem SeenLE.mono {η : TEnv} {V V' : Ts} (h : SeenLE η V) (hV : V ≤ V') : SeenLE η V' :=
  fun l hl => let ⟨f, h1, h2⟩ := h l hl; ⟨f, h1, Nat.le_trans h2 hV⟩

/-- (D3) A word with its view raised to at least `V`. -/
def bumpW (V : Ts) (w : Word) : Word := { w with view := max w.view V }

theorem WLe_bump (V : Ts) : ∀ ws : List Word, WLe ws (ws.map (bumpW V))
  | [] => WLe_refl []
  | w :: ws => ⟨⟨rfl, fun _ _ _ => Nat.le_max_left _ _⟩, WLe_bump V ws⟩

theorem LocAbove_bump (V : Ts) (ws : List Word) : LocAbove V (ws.map (bumpW V)) := by
  intro w hw _ _ _
  obtain ⟨w', _, rfl⟩ := List.mem_map.1 hw
  exact Nat.le_max_right _ _

/-- (D3) **A value stored is a memory value** once its pointers' views are at
least `V`, when every `seen` label's frontier is at most `V`. -/
theorem EnvVal.store {η : TEnv} {T : Ty} {ws : List Word} {V : Ts} (h : EnvVal η T ws) (hS : SeenLE η V) :
    ValOf η T (ws.map (bumpW V)) :=
  ⟨VR_unsee V T (CE η) (CE η.unsee) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl)) (fun _ _ h => h) (LocAbove_bump V ws)
      (VR_up _ _ _ _ (WLe_bump V ws) h.1),
    Valid_vals _ _ _ (WLe_bump V ws).vals h.2⟩

/-- (D3) A memory value is a value in the thread's view. -/
theorem ValOf.env {η : TEnv} {T : Ty} {ws : List Word} (h : ValOf η T ws) : EnvVal η T ws :=
  ⟨VR_mono T (CE η.unsee) (CE η) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) h.1, h.2⟩

/-- (D3) A message as a word: its value and its view (the view a load of it
hands back; the read timestamp is irrelevant to `WLe1`). -/
def mw (m : Msg) : Word := ⟨m.val, m.view, 0⟩

/-- (D3) A word `w` stored with message view `mv` at least its view, if a
pointer, is at least as viewed as the message word. -/
theorem WLe1_msg {w0 w : Word} {mv : Ts} (h : WLe1 w0 w) (hv : ∀ x g, w.val = .loc x g → w.view ≤ mv) :
    WLe1 w0 ⟨w.val, mv, 0⟩ :=
  ⟨h.1, fun x g hx => Nat.le_trans (h.2 x g hx) (hv x g (h.1 ▸ hx))⟩

/-- (D3) The same, for a bumped word: the message view covers `V` as well. -/
theorem WLe1_msgB {w0 w : Word} {V mv : Ts} (h : WLe1 w0 (bumpW V w))
    (hv : ∀ x g, w.val = .loc x g → w.view ≤ mv) (hV : V ≤ mv) : WLe1 w0 ⟨w.val, mv, 0⟩ :=
  ⟨h.1, fun x g hx => Nat.le_trans (h.2 x g hx) (Nat.max_le.2 ⟨hv x g (h.1 ▸ hx), hV⟩)⟩

/-- (M4b) A memory value of `S` with `S`'s word count: what a torn read of a
published cell splices (`TermTear.VR_tearIn` needs the lengths). -/
def ValOfS (η : TEnv) (S : Ty) (ws : List Word) : Prop := ValOf η S ws ∧ ShapeC S ws

/-- (T3c-5b) A segment of a cell of type `T`: of type `S`, starting at word
`b`.  The whole cell (at 0), or slot `j` of a buffer `array (lit N) S`. -/
def SegOf (T : Ty) (b : Nat) (S : Ty) : Prop :=
  (b = 0 ∧ S = T ∧ accs T ≠ none) ∨ ∃ N us j, T = .array (.lit N) S ∧ accs S = some us ∧ j < N ∧ b = j * nWords us

/-- Word `o` of a cell of type `T` may hold `v`: it is a word of some value of
a segment's type, at its place in the segment. -/
def WordOK (η : TEnv) (T : Ty) (o : Nat) (w : Word) : Prop :=
  ∃ b S ws o' w0, SegOf T b S ∧ ValOfS η S ws ∧ ws[o']? = some w0 ∧ WLe1 w0 w ∧ b + o' = o

/-- Words `o`, `o+1` may hold `v0`, `v1` together: they are two words of one
value of a segment's type. -/
def PairOK (η : TEnv) (T : Ty) (o : Nat) (w0 w1 : Word) : Prop :=
  ∃ b S ws o' x0 x1, SegOf T b S ∧ ValOfS η S ws ∧ ws[o']? = some x0 ∧ ws[o' + 1]? = some x1 ∧
    WLe1 x0 w0 ∧ WLe1 x1 w1 ∧ b + o' = o

/-- **The memory invariant.** -/
def MemOK (η : TEnv) (mem : Memory) (pairs : List Ts) : Prop :=
  (∀ (t : Ts) (m : Msg) (c : Cell), mem[t]? = some m → η.sto m.loc.label = some c →
     m.val = .undef ∨ WordOK η c.ty m.loc.offset (mw m)) ∧
  (∀ (t : Ts) (m0 m1 : Msg) (c : Cell), t ∈ pairs → mem[t]? = some m0 → mem[t + 1]? = some m1 →
     η.sto m0.loc.label = some c → PairOK η c.ty m0.loc.offset (mw m0) (mw m1)) ∧
  (∀ t, t ∈ pairs → t + 1 < mem.size)

/-- `a`'s coherence view is at a message holding `v`, and nothing is written to
`a` after it. -/
def Latest (mem : Memory) (coh : Address → Ts) (a : Address) (w : Word) : Prop :=
  (∃ m, mem[coh a]? = some m ∧ m.loc = a ∧ m.val = w.val ∧ ∀ x g, w.val = .loc x g → w.view ≤ m.view) ∧
  ∀ (t : Ts) (m : Msg), coh a < t → mem[t]? = some m → m.loc ≠ a

/-- (T3c-5b) A buffer's words: `N` slots of `e`, of which the first `n` (at
most `N`) are initialised, each a value of `e`. -/
def BufOK (η : TEnv) (n : Nat) (T : Ty) (vals : List Word) : Prop :=
  ∃ N e us, T = .array (.lit N) e ∧ accs e = some us ∧ n ≤ N ∧ vals.length = N * nWords us ∧
    ∀ j, j < n → ValOf η e ((vals.drop (j * nWords us)).take (nWords us))

/-- The words of a cell of type `T`: a value of `T`, as many words as `T`'s
word count; or (T3c-5b) a buffer, `n` slots initialised. -/
def CellOK (η : TEnv) (n : Nat) (T : Ty) (vals : List Word) : Prop :=
  (wc T = some vals.length ∧ ValOf η T vals) ∨ BufOK η n T vals

/-- **The owner's invariant**: each own cell of thread `η.tid`, word by word,
is at its latest message, and those words are OK for the cell (`CellOK`; a
buffer's initialised count is the ghost `η.ini`). -/
def OwnOK (η : TEnv) (mem : Memory) (vs : VState) : Prop :=
  ∀ l c, η.sto l = some c → c.owner = some η.tid →
    ∃ vals, CellOK η (η.ini l) c.ty vals ∧
      ∀ o v, vals[o]? = some v → Latest mem vs.coh ⟨l, o⟩ v

/-- (M2b) **Placeholders at `⟨l, o⟩` are hidden below `V`**: a message there
that is not a word of a value of the cell's type `T` (an allocation's `undef`)
has a later message to `⟨l, o⟩` at a timestamp at most `V`. A load whose read
bound reaches `V` cannot read it (`hiddenFrom`). -/
def Hidden (η : TEnv) (T : Ty) (mem : Memory) (l : AllocLabel) (o : Nat) (V : Ts) : Prop :=
  ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc = ⟨l, o⟩ → ¬ WordOK η T o (mw m) →
    ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ V ∧ mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩

/-- (M2b) Offset `o` of cell `c` (at `l`) is initialised: any offset of a
value cell; of a buffer `array (lit N) e`, one in the first `η.ini l` slots. -/
def InitR (η : TEnv) (c : Cell) (l : AllocLabel) (o : Nat) : Prop :=
  ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → o < η.ini l * nWords us

/-- (M2b) The owner's placeholders are hidden below its `vWr`: what a
`dmb ishst` makes the publication frontier. -/
def OwnHid (η : TEnv) (mem : Memory) (vs : VState) : Prop :=
  ∀ l c, η.sto l = some c → c.owner = some η.tid → ∀ o, InitR η c l o → Hidden η c.ty mem l o vs.vWr

/-- (M2b) A published cell's placeholders are hidden below its frontier.  The
thread's own cells are left to `OwnHid` (and `coh`): a stale own handle may
still initialise a buffer slot after publication, below its own `vWr` but not
below the frontier. -/
def PubDef (η : TEnv) (mem : Memory) : Prop :=
  ∀ l c f, η.sto l = some c → c.owner ≠ some η.tid → η.pfr l = some f → ∀ o, InitR η c l o →
    Hidden η c.ty mem l o f

/-- An access list's word count is the type's `wc`. -/
theorem wc_of_accs {T : Ty} {us : List Acc} (h : accs T = some us) : wc T = some (nWords us) := by
  simp [wc, h]

/-- (M4b) Words as many as the word count have the type's shape. -/
theorem ShapeC_of_wc {T : Ty} {ws : List Word} {n : Nat} (hw : wc T = some n) (hl : ws.length = n) :
    ShapeC T ws :=
  fun us hu => by rw [wc_of_accs hu] at hw; rw [hl]; exact (Option.some.inj hw).symm

/-- A type with a word count is not a buffer. -/
theorem notArr_of_wc {T : Ty} {k : Nat} (h : wc T = some k) : ∀ N e, T ≠ .array (.lit N) e := by
  intro N e hT; subst hT; simp [wc, accs] at h

/-- Not a buffer: a cell's words are a value of its type. -/
theorem CellOK.plain {η : TEnv} {n : Nat} {T : Ty} {vals : List Word} (h : CellOK η n T vals)
    (hT : ∀ N e, T ≠ .array (.lit N) e) : wc T = some vals.length ∧ ValOf η T vals := by
  rcases h with h | ⟨N, e, _, hT', _⟩
  · exact h
  · exact absurd hT' (hT N e)

theorem OwnOK_plain {η : TEnv} {mem : Memory} {vs : VState} {l : AllocLabel} {c : Cell}
    (ho : OwnOK η mem vs) (hc : η.sto l = some c) (hown : c.owner = some η.tid)
    (hT : ∀ N e, c.ty ≠ .array (.lit N) e) :
    ∃ vals, wc c.ty = some vals.length ∧ ValOf η c.ty vals ∧
      ∀ o v, vals[o]? = some v → Latest mem vs.coh ⟨l, o⟩ v := by
  obtain ⟨vals, h1, h2⟩ := ho l c hc hown
  obtain ⟨h3, h4⟩ := h1.plain hT
  exact ⟨vals, h3, h4, h2⟩

theorem WordOK_whole {η : TEnv} {T : Ty} {vs : List Word} {o : Nat} {v : Word} (hv : ValOfS η T vs)
    (ha : accs T ≠ none) (h : vs[o]? = some v) : WordOK η T o v :=
  ⟨0, T, vs, o, v, Or.inl ⟨rfl, rfl, ha⟩, hv, h, WLe1_refl v, Nat.zero_add o⟩

theorem WordOK_map {η₁ η₂ : TEnv} (f : ∀ {U : Ty} {vs : List Word}, ValOf η₁ U vs → ValOf η₂ U vs)
    {T : Ty} {o : Nat} {v : Word} (h : WordOK η₁ T o v) : WordOK η₂ T o v := by
  obtain ⟨b, S, vs, o', w0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨b, S, vs, o', w0, h1, ⟨f h2.1, h2.2⟩, h3, h4, h5⟩

theorem PairOK_map {η₁ η₂ : TEnv} (f : ∀ {U : Ty} {vs : List Word}, ValOf η₁ U vs → ValOf η₂ U vs)
    {T : Ty} {o : Nat} {v0 v1 : Word} (h : PairOK η₁ T o v0 v1) : PairOK η₂ T o v0 v1 := by
  obtain ⟨b, S, vs, o', x0, x1, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨b, S, vs, o', x0, x1, h1, ⟨f h2.1, h2.2⟩, h3, h4, h5, h6, h7⟩

theorem CellOK_map {η₁ η₂ : TEnv} (f : ∀ {U : Ty} {vs : List Word}, ValOf η₁ U vs → ValOf η₂ U vs)
    {n m : Nat} (hm : m ≤ n) {T : Ty} {vals : List Word} (h : CellOK η₁ n T vals) : CellOK η₂ m T vals := by
  rcases h with ⟨h1, h2⟩ | ⟨N, e, us, h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h1, f h2⟩
  · exact Or.inr ⟨N, e, us, h1, h2, Nat.le_trans hm h3, h4, fun j hj => f (h5 j (Nat.lt_of_lt_of_le hj hm))⟩

/-! ## §2 Loads at a latest address -/

/-- **Only the latest message is readable** when coherence is at it and nothing
follows it: anything older is hidden by it, and nothing newer exists. -/
theorem readable_latest {mem : Memory} {coh : Address → Ts} {a : Address} {v : Word} {t bound : Ts}
    (hl : Latest mem coh a v) (hb : coh a ≤ bound) (hr : WeakMem.readable mem a t bound = true) :
    t = coh a := by
  obtain ⟨⟨m, hm, hma, _⟩, hnone⟩ := hl
  rcases Nat.lt_trichotomy t (coh a) with h | h | h
  · exfalso
    have hh : WeakMem.hiddenFrom mem a t bound = true := by
      unfold WeakMem.hiddenFrom
      rw [List.any_eq_true]
      exact ⟨coh a, List.mem_range.2 (Nat.lt_succ_of_le hb), by simp [h, hm, hma]⟩
    simp [WeakMem.readable, hh] at hr
  · exact h
  · exfalso
    unfold WeakMem.readable at hr
    cases ht : mem[t]? with
    | none => simp [ht] at hr
    | some m' =>
        simp [ht] at hr
        exact hnone t m' h ht hr.1

theorem coh_le_readBound (arch : Arch) (vs : VState) (dv : Ts) (a : Address) :
    vs.coh a ≤ Promises.readBoundOf arch vs dv a := by
  simp only [Promises.readBoundOf]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

/-- **A one-word load at a latest address** returns its value and leaves
coherence as it was. -/
theorem stepLoad_latest {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool} {v : Word}
    (hl : Latest mem th.vs.coh a v) (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) :
    WLe1 v (th'.regs dst) ∧ th'.vs.coh = th.vs.coh := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨_, hr⟩, rfl⟩ := h
  have e := readable_latest hl (coh_le_readBound arch th.vs _ a) hr
  subst e
  obtain ⟨⟨m, hm, _, hv, hvw⟩, _⟩ := hl
  refine ⟨⟨?_, fun x g hx => ?_⟩, ?_⟩
  · simp [getElem!_def, hm, hv]
  · simpa [getElem!_def, hm] using hvw x g hx
  · funext b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]

/-- **A two-word load at latest addresses** returns both values and leaves
coherence as it was. -/
theorem stepLoadPair_latest {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool} {v0 v1 : Word}
    (hd : dst0 ≠ dst1) (hl0 : Latest mem th.vs.coh a v0) (hl1 : Latest mem th.vs.coh a.next v1)
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th dst0 dst1 a deps acq) :
    WLe1 v0 (th'.regs dst0) ∧ WLe1 v1 (th'.regs dst1) ∧ th'.vs.coh = th.vs.coh := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, hs⟩ := h
  have e0 := readable_latest hl0 (coh_le_readBound arch th.vs _ a) hr0
  have e1 := readable_latest hl1 (coh_le_readBound arch th.vs _ a.next) hr1
  subst e0 e1
  split at hs
  · exact absurd hs (by simp)
  · simp only [Option.some.injEq] at hs
    subst hs
    obtain ⟨⟨m0, hm0, _, hv0, hw0⟩, _⟩ := hl0
    obtain ⟨⟨m1, hm1, _, hv1, hw1⟩, _⟩ := hl1
    refine ⟨⟨?_, fun x g hx => ?_⟩, ⟨?_, fun x g hx => ?_⟩, ?_⟩
    · simp [getElem!_def, hm0, hv0]
    · simpa [getElem!_def, hm0] using hw0 x g hx
    · simp [getElem!_def, hm1, hv1, Ne.symm hd]
    · simpa [getElem!_def, hm1, Ne.symm hd] using hw1 x g hx
    · funext b
      by_cases hb : b = a
      · subst hb; simp
      · by_cases hb' : b = a.next
        · subst hb'; simp [hb]
        · simp [hb, hb']

/-- **Loading latest words** (an own cell, T3c-4): `loadUnits` returns exactly
the latest values, and changes neither memory nor coherence. -/
theorem loadUnits_latest {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (vals : List Word), vals.length = nWords us →
      (∀ j v, vals[j]? = some v → Latest s.mem s.vs.coh (offs a (k + j)) v) →
      ∀ r, r ∈ loadUnits arch pw a acq us k s →
        WLe vals r.2 ∧ r.1.vs.coh = s.vs.coh ∧ r.1.mem = s.mem
  | [], k, s, vals, hn, _, r, hr => by
      have : vals = [] := List.eq_nil_of_length_eq_zero (by simpa [nWords] using hn)
      subst this
      simp only [loadUnits, List.mem_singleton] at hr
      subst hr; exact ⟨WLe_refl [], rfl, rfl⟩
  | .one :: us, k, s, vals, hn, hl, r, hr => by
      cases vals with
      | nil => simp [nWords, Acc.size] at hn; omega
      | cons v rest =>
          simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
          obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
          have hl0 : Latest s.mem s.vs.coh (offs a k) v := by
            have := hl 0 v rfl; simpa using this
          obtain ⟨hv, hc⟩ := stepLoad_latest (th := mth s pw pw pw) hl0 hth
          have hn' : rest.length = nWords us := by
            simp [nWords, Acc.size] at hn ⊢; omega
          have ih := loadUnits_latest us (k + 1)
            { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] } rest hn'
            (fun j v' hj => by
              have := hl (j + 1) v' (by simpa using hj)
              simp only [hc]
              rw [show k + 1 + j = k + (j + 1) by omega]
              exact this) (s', ws) hmem
          obtain ⟨h1, h2, h3⟩ := ih
          refine ⟨⟨hv, h1⟩, ?_, ?_⟩
          · rw [h2]; exact hc
          · exact h3
  | .two :: us, k, s, vals, hn, hl, r, hr => by
      match vals, hn, hl with
      | [], hn, _ => simp [nWords, Acc.size] at hn; omega
      | [_], hn, _ => simp [nWords, Acc.size] at hn; omega
      | v0 :: v1 :: rest, hn, hl =>
          simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
          obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
          have hl0 : Latest s.mem s.vs.coh (offs a k) v0 := by
            have := hl 0 v0 rfl; simpa using this
          have hl1 : Latest s.mem s.vs.coh (offs a k).next v1 := by
            have := hl 1 v1 rfl
            have e : (offs a k).next = offs a (k + 1) := by simp [offs, WeakMem.Address.next, Nat.add_assoc]
            rw [e]; simpa using this
          obtain ⟨hv0, hv1, hc⟩ := stepLoadPair_latest (th := mth s pw pw pw) (by decide) hl0 hl1 hth
          have hn' : rest.length = nWords us := by
            simp only [List.length_cons, nWords, List.map_cons, List.sum_cons, Acc.size] at hn ⊢; omega
          have ih := loadUnits_latest us (k + 2)
            { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] } rest hn'
            (fun j v' hj => by
              have := hl (j + 2) v' (by simpa using hj)
              simp only [hc]
              rw [show k + 2 + j = k + (j + 2) by omega]
              exact this) (s', ws) hmem
          obtain ⟨h1, h2, h3⟩ := ih
          refine ⟨⟨hv0, hv1, h1⟩, ?_, ?_⟩
          · rw [h2]; exact hc
          · exact h3

/-! ## §3 Stores -/

/-- The value a store operand denotes. -/
def exprVal (th : Promises.Thread) : WeakMem.Expr → Val
  | .const c => c
  | .reg r => (th.regs r).val

theorem push_lt {mem : Memory} {m : Msg} {i : Nat} (hi : i < mem.size) : (mem.push m)[i]? = mem[i]? := by
  rw [Array.getElem?_push]; simp [Nat.ne_of_lt hi]

/-- Appending a message that is OK at its cell keeps the invariant. -/
theorem MemOK_push {η : TEnv} {mem : Memory} {pairs : List Ts} (h : MemOK η mem pairs) (m : Msg)
    (hm : ∀ c, η.sto m.loc.label = some c → m.val = .undef ∨ WordOK η c.ty m.loc.offset (mw m)) :
    MemOK η (mem.push m) pairs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t m' c ht hc => ?_, fun t m0 m1 c hp h0 h1' hc => ?_, fun t hp => ?_⟩
  · rw [Array.getElem?_push] at ht
    split at ht
    · simp only [Option.some.injEq] at ht; subst ht; exact hm c hc
    · exact h1 t m' c ht hc
  · have hl := h3 t hp
    rw [push_lt (Nat.lt_of_succ_lt hl)] at h0
    rw [push_lt hl] at h1'
    exact h2 t m0 m1 c hp h0 h1' hc
  · simp only [Array.size_push]; exact Nat.lt_succ_of_lt (h3 t hp)

/-- **A one-word store** either appends its message (at the top) or fulfils
one of the thread's promises, a message already there with the same value;
either way coherence at `a` moves to it. -/
theorem stepStore_cases {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    ∃ t, ((mem' = mem.push ⟨a, exprVal th e, Promises.storeMview th e deps rel⟩ ∧ t = mem.size ∧
            th'.promises = th.promises) ∨
          (mem' = mem ∧ t ∈ th.promises ∧ ∃ m, mem[t]? = some m ∧ m.loc = a ∧ m.val = exprVal th e ∧
            Promises.storeMview th e deps rel ≤ m.view)) ∧
      th'.vs.coh = (fun b => if b = a then t else th.vs.coh b) ∧ th'.vs.vRelSt = th.vs.vRelSt := by
  cases e with
  | const c =>
      simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
      rcases h with h | ⟨t, htp, hf⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨mem.size, Or.inl ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
      · cases hm : mem[t]? with
        | none => simp [hm] at hf
        | some m =>
            simp only [hm] at hf
            split at hf
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
              exact ⟨t, Or.inr ⟨rfl, htp, m, hm, hcond.1.1.1, hcond.1.1.2, hcond.1.2⟩, rfl, rfl⟩
            · simp at hf
  | reg r =>
      simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
      rcases h with h | ⟨t, htp, hf⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨mem.size, Or.inl ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
      · cases hm : mem[t]? with
        | none => simp [hm] at hf
        | some m =>
            simp only [hm] at hf
            split at hf
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
              exact ⟨t, Or.inr ⟨rfl, htp, m, hm, hcond.1.1.1, hcond.1.1.2, hcond.1.2⟩, rfl, rfl⟩
            · simp at hf

theorem exprVal_dataE (th : Promises.Thread) (r : WeakMem.Reg) (w : Word) (hr : th.regs r = w) :
    exprVal th (dataE r w) = w.val := by
  unfold dataE
  cases hw : w.val <;> simp [exprVal, hr, hw]

/-- (D3) A store's message view covers the release view. -/
theorem storeMview_relSt (th : Promises.Thread) (e : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    th.vs.vRelSt ≤ Promises.storeMview th e deps rel := by
  simp only [Promises.storeMview]
  split
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  · exact Nat.le_max_left _ _

/-- (D3) **A stored pointer's view flows into its message**: `dataE` stores a
`.loc` word through its register. -/
theorem storeMview_dataE (th : Promises.Thread) (r : WeakMem.Reg) (w : Word) (hr : th.regs r = w)
    (deps : List WeakMem.Reg) (rel : Bool) :
    ∀ x g, w.val = .loc x g → w.view ≤ Promises.storeMview th (dataE r w) deps rel := by
  intro x g hx
  simp only [dataE, hx, Promises.storeMview, hr]
  split
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem add_shift1 (o i j : Nat) : o + (i + 1) + j = o + i + (j + 1) := by omega
theorem add_shift2 (o i j : Nat) : o + (i + 2) + j = o + i + (j + 2) := by omega

/-- A pair store's two messages, in `exprVal` form. -/
theorem stepStorePair_eq (mem : Memory) (pairs : List Ts) (th : Promises.Thread) (a : Address)
    (e0 e1 : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1 =
      (mem.push ⟨a, exprVal th e0, max (Promises.storeMview th e0 deps rel) (Promises.storeMview th e1 deps rel)⟩).push
        ⟨a.next, exprVal th e1, max (Promises.storeMview th e0 deps rel) (Promises.storeMview th e1 deps rel)⟩ ∧
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.1 = pairs ++ [mem.size] ∧
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs.coh =
      (fun b => if b = a then mem.size else if b = a.next then mem.size + 1 else th.vs.coh b) ∧
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.promises = th.promises ∧
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs.vRelSt = th.vs.vRelSt := by
  cases e0 <;> cases e1 <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Appending a pair store's two messages, two words of one value, keeps the
invariant. -/
theorem MemOK_pushPair {η : TEnv} {mem : Memory} {pairs : List Ts} (h : MemOK η mem pairs)
    (a : Address) (v0 v1 : Val) (mv : Ts)
    (hok : ∀ c, η.sto a.label = some c → PairOK η c.ty a.offset ⟨v0, mv, 0⟩ ⟨v1, mv, 0⟩) :
    MemOK η ((mem.push ⟨a, v0, mv⟩).push ⟨a.next, v1, mv⟩) (pairs ++ [mem.size]) := by
  have hA := MemOK_push (MemOK_push h ⟨a, v0, mv⟩ fun c hc => by
      obtain ⟨b, S, vs, o', x0, _, hs, hv, h0, _, l0, _, he⟩ := hok c hc
      exact Or.inr ⟨b, S, vs, o', x0, hs, hv, h0, l0, he⟩)
    ⟨a.next, v1, mv⟩ fun c hc => by
      obtain ⟨b, S, vs, o', _, x1, hs, hv, _, h1, _, l1, he⟩ := hok c hc
      exact Or.inr ⟨b, S, vs, o' + 1, x1, hs, hv, h1, l1,
        by show b + (o' + 1) = a.offset + 1; rw [← he]; rfl⟩
  obtain ⟨f1, f2, f3⟩ := hA
  refine ⟨f1, fun t n0 n1 c hp hn0 hn1 hc => ?_, fun t hp => ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact f2 t n0 n1 c hp hn0 hn1 hc
    · simp only [List.mem_singleton] at hp
      subst hp
      rw [push_lt (by simp), Array.getElem?_push_size] at hn0
      rw [show mem.size + 1 = (mem.push ⟨a, v0, mv⟩).size from (Array.size_push _).symm,
        Array.getElem?_push_size] at hn1
      simp only [Option.some.injEq] at hn0 hn1
      subst hn0 hn1
      exact hok c hc
  · rcases List.mem_append.1 hp with hp | hp
    · exact f3 t hp
    · simp only [List.mem_singleton] at hp; subst hp; simp

/-- **Storing a slice of one value** keeps the invariant: every stored word is
that value's word at its offset (and a pair is two of its words). -/
theorem storeUnits_memOK {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {η : TEnv} {c : Cell} {b o0 : Nat} {S : Ty} {vals : List Word} {V : Ts} (hc : η.sto a.label = some c)
    (hseg : SegOf c.ty b S) (hbo : a.offset = b + o0) (hv : ValOfS η S vals) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St),
      (∀ (j : Nat) w, ws[j]? = some w → ∃ w0, vals[o0 + i + j]? = some w0 ∧ WLe1 w0 (bumpW V w)) →
      V ≤ s.vs.vRelSt →
      MemOK η s.mem s.pairs → ∀ s', s' ∈ storeUnits k arch pw a rel us ws i s → MemOK η s'.mem s'.pairs
  | [], _, _, s, _, _, hm, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hm
  | .one :: us, w :: ws, i, s, hw, hV, hm, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, hcase, _, hrs⟩ := stepStore_cases hst
      have hm' : MemOK η mem' s.pairs := by
        rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · refine MemOK_push hm _ fun c' hc' => Or.inr ?_
          simp only [offs] at hc' ⊢
          rw [hc] at hc'; cases hc'
          obtain ⟨w0, hw0, hle⟩ := hw 0 w rfl
          refine ⟨b, S, vals, o0 + i, w0, hseg, hv, by simpa using hw0, ?_, by rw [hbo, Nat.add_assoc]⟩
          show WLe1 w0 ⟨exprVal _ (dataE 1 w), Promises.storeMview _ (dataE 1 w) [0] rel, 0⟩
          rw [exprVal_dataE _ 1 w (by simp [mth, regsOf])]
          exact WLe1_msgB hle (storeMview_dataE _ 1 w (by simp [mth, regsOf]) [0] rel)
            (Nat.le_trans hV (storeMview_relSt (mth s pw w w) _ [0] rel))
        · exact hm
      exact storeUnits_memOK hc hseg hbo hv us ws (i + 1) _
        (fun j w' hj => by
          have := hw (j + 1) w' (by simpa using hj)
          rw [add_shift1]; exact this)
        (by show V ≤ th.vs.vRelSt; rw [hrs]; exact hV)
        hm' s' hs
  | .two :: us, w0 :: w1 :: ws, i, s, hw, hV, hm, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨x0, h0, l0⟩ := hw 0 w0 rfl
      obtain ⟨x1, h1, l1⟩ := hw 1 w1 rfl
      simp only [Nat.add_zero] at h0
      have e0 : exprVal (mth s pw w0 w1) (dataE 1 w0) = w0.val :=
        exprVal_dataE _ 1 w0 (by simp [mth, regsOf])
      have e1 : exprVal (mth s pw w0 w1) (dataE 2 w1) = w1.val :=
        exprVal_dataE _ 2 w1 (by simp [mth, regsOf])
      obtain ⟨q1, q2, -, -, q5⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      refine storeUnits_memOK hc hseg hbo hv us ws (i + 2) _
        (fun j w' hj => by
          have := hw (j + 2) w' (by simpa using hj)
          rw [add_shift2]; exact this)
        (by rw [q5]; exact hV) ?_ s' hs
      show MemOK η (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel).1
        (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel).2.1
      rw [q1, q2, e0, e1]
      refine MemOK_pushPair hm (offs a i) w0.val w1.val _ fun c' hc' => ?_
      simp only [offs] at hc' ⊢
      rw [hc] at hc'; cases hc'
      have hV0 : V ≤ max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel) :=
        Nat.le_trans hV (Nat.le_trans (storeMview_relSt (mth s pw w0 w1) _ [0] rel) (Nat.le_max_left _ _))
      refine ⟨b, S, vals, o0 + i, x0, x1, hseg, hv, h0, h1, WLe1_msgB l0 (fun x g hx => ?_) hV0,
        WLe1_msgB l1 (fun x g hx => ?_) hV0, by rw [hbo, Nat.add_assoc]⟩
      · exact Nat.le_trans (storeMview_dataE _ 1 w0 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_left _ _)
      · exact Nat.le_trans (storeMview_dataE _ 2 w1 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_right _ _)
  | .one :: _, [], _, _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, _, _, s', hs => by simp [storeUnits] at hs

/-! ## §4 Growing Σ; the owner's view across stores -/

theorem ValOf_mono {η₁ η₂ : TEnv} (hp : η₁.prog = η₂.prog) (ht : η₁.tid = η₂.tid)
    (hs : ∀ l c, η₁.sto l = some c → η₂.sto l = some c) (hi : ∀ l, η₁.ini l ≤ η₂.ini l)
    {T : Ty} {vs : List Word} (h : ValOf η₁ T vs)
    (hP : ∀ l f, η₁.pfr l = some f → η₂.pfr l = some f := by first | exact fun _ _ h => h | simp_all)
    (hS : ∀ l, η₁.seen l → η₂.seen l := by first | exact fun _ h => h | simp_all)
    (hB : ∀ l B, η₁.box l = some B → η₂.box l = some B := by first | exact fun _ _ h => h | simp_all)
    (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) :
    ValOf η₂ T vs := by
  obtain ⟨hv, hV⟩ := h
  exact ⟨VR_mono T (CE η₁.unsee) (CE η₂.unsee) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl hp ht hs hi hP
    (fun _ h => h) hB hv hri, hV⟩

/-- **Σ grows** (allocation): the invariant survives, provided no message sits
at a newly typed cell. -/
theorem MemOK_mono {η₁ η₂ : TEnv} {mem : Memory} {pairs : List Ts} (h : MemOK η₁ mem pairs)
    (hp : η₁.prog = η₂.prog) (ht : η₁.tid = η₂.tid) (hs : ∀ l c, η₁.sto l = some c → η₂.sto l = some c)
    (hi : ∀ l, η₁.ini l ≤ η₂.ini l) (hnew : ∀ (t : Ts) (m : Msg) c, mem[t]? = some m → η₂.sto m.loc.label = some c →
      η₁.sto m.loc.label = some c)
    (hP : ∀ l f, η₁.pfr l = some f → η₂.pfr l = some f := by first | exact fun _ _ h => h | simp_all)
    (hS : ∀ l, η₁.seen l → η₂.seen l := by first | exact fun _ h => h | simp_all)
    (hB : ∀ l B, η₁.box l = some B → η₂.box l = some B := by first | exact fun _ _ h => h | simp_all)
    (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) :
    MemOK η₂ mem pairs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t m c ht' hc => ?_, fun t m0 m1 c hp' h0 h1' hc => ?_, h3⟩
  · rcases h1 t m c ht' (hnew t m c ht' hc) with hu | hw
    · exact Or.inl hu
    · exact Or.inr (WordOK_map (fun h => ValOf_mono hp ht hs hi h hP hS hB hri) hw)
  · exact PairOK_map (fun h => ValOf_mono hp ht hs hi h hP hS hB hri) (h2 t m0 m1 c hp' h0 h1' (hnew t m0 c h0 hc))

theorem lt_of_get {mem : Memory} {i : Nat} {m : Msg} (h : mem[i]? = some m) : i < mem.size := by
  rcases Nat.lt_or_ge i mem.size with hi | hi
  · exact hi
  · rw [Array.getElem?_eq_none hi] at h; cases h

/-- A message appended at `a`, with coherence moved to it, is `a`'s latest. -/
theorem Latest_push_top {mem : Memory} {coh : Address → Ts} {a : Address} {v : Word} {mv : Ts}
    (hc : coh a = mem.size) (hv : ∀ x g, v.val = .loc x g → v.view ≤ mv) :
    Latest (mem.push ⟨a, v.val, mv⟩) coh a v := by
  refine ⟨⟨_, by rw [hc, Array.getElem?_push_size], rfl, rfl, hv⟩, fun t m ht hm => ?_⟩
  rw [hc] at ht
  rw [Array.getElem?_push] at hm
  split at hm
  · rename_i he; exact absurd he (Nat.ne_of_gt ht)
  · rw [Array.getElem?_eq_none (Nat.le_of_lt ht)] at hm; cases hm

/-- A message appended elsewhere leaves `b`'s latest as it was. -/
theorem Latest_push_other {mem : Memory} {coh coh' : Address → Ts} {a b : Address} {v : Word} {v' : Val} {mv : Ts}
    (hl : Latest mem coh b v) (hb : b ≠ a) (hc : coh' b = coh b) :
    Latest (mem.push ⟨a, v', mv⟩) coh' b v := by
  obtain ⟨⟨m, hm, hma, hmv, hmw⟩, hn⟩ := hl
  refine ⟨⟨m, by rw [hc, push_lt (lt_of_get hm)]; exact hm, hma, hmv, hmw⟩, fun t m' ht hm' => ?_⟩
  rw [hc] at ht
  rw [Array.getElem?_push] at hm'
  split at hm'
  · simp only [Option.some.injEq] at hm'; subst hm'; exact Ne.symm hb
  · exact hn t m' ht hm'

theorem offs_ne (a : Address) {x y : Nat} (h : x ≠ y) : offs a x ≠ offs a y := by
  intro e; apply h
  have := congrArg WeakMem.Address.offset e
  simp only [offs] at this
  exact Nat.add_left_cancel this

theorem offs_next (a : Address) (i : Nat) : (offs a i).next = offs a (i + 1) := by
  simp [offs, WeakMem.Address.next, Nat.add_assoc]

theorem nWords_one (us : List Acc) : nWords (.one :: us) = nWords us + 1 := by
  simp [nWords, Acc.size]; omega
theorem nWords_two (us : List Acc) : nWords (.two :: us) = nWords us + 2 := by
  simp [nWords, Acc.size]; omega

/-- No outstanding promise of the thread is at label `l` (so its stores there
append rather than fulfil). -/
def NoProm (s : St) (l : AllocLabel) : Prop :=
  ∀ t, t ∈ s.promises → t < s.mem.size ∧ ∀ m, s.mem[t]? = some m → m.loc.label ≠ l

theorem NoProm_push {s : St} {l : AllocLabel} (h : NoProm s l) (m : Msg) (s' : St)
    (hm : s'.mem = s.mem.push m) (hp : s'.promises = s.promises) : NoProm s' l := by
  intro t ht
  rw [hp] at ht
  obtain ⟨hlt, hl⟩ := h t ht
  refine ⟨by rw [hm, Array.size_push]; exact Nat.lt_succ_of_lt hlt, fun m' hm' => ?_⟩
  rw [hm, push_lt hlt] at hm'
  exact hl m' hm'

/-- **Storing words, as their owner sees it**: with no outstanding promise at
the cell, each stored word becomes its address's latest, and every other
address keeps its latest. -/
theorem storeUnits_latest {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St) (V : Ts), NoProm s a.label → V ≤ s.vs.vRelSt →
      ∀ s', s' ∈ storeUnits k arch pw a rel us ws i s →
        NoProm s' a.label ∧
        (∀ (j : Nat) w, j < nWords us → ws[j]? = some w → Latest s'.mem s'.vs.coh (offs a (i + j)) (bumpW V w)) ∧
        (∀ (b : Address) (v : Word), (∀ j : Nat, j < nWords us → b ≠ offs a (i + j)) →
          Latest s.mem s.vs.coh b v → Latest s'.mem s'.vs.coh b v)
  | [], _, _, s, _, hn, _, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      exact ⟨hn, fun j _ hj => absurd hj (by simp [nWords]), fun _ _ _ h => h⟩
  | .one :: us, w :: ws, i, s, V, hn, hV, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, hcase, hcoh, hrs⟩ := stepStore_cases hst
      rcases hcase with ⟨hmem, rfl, hprom⟩ | ⟨_, htp, m, hm, hma, _⟩
      · rw [exprVal_dataE _ 1 w (by simp [mth, regsOf])] at hmem
        let s1 : St := { s with mem := mem', vs := th.vs, promises := th.promises }
        have hn1 : NoProm s1 a.label := NoProm_push hn _ s1 hmem hprom
        obtain ⟨g1, g2, g3⟩ := storeUnits_latest us ws (i + 1) s1 V hn1 (by show V ≤ th.vs.vRelSt; rw [hrs]; exact hV) s' hs
        have hl1 : Latest s1.mem s1.vs.coh (offs a i) (bumpW V w) := by
          show Latest mem' th.vs.coh (offs a i) (bumpW V w)
          rw [hmem]; exact Latest_push_top (v := bumpW V w) (by rw [hcoh]; simp) fun x g hx =>
            Nat.max_le.2 ⟨storeMview_dataE _ 1 w (by simp [mth, regsOf]) [0] rel x g hx,
              Nat.le_trans hV (storeMview_relSt (mth s pw w w) _ [0] rel)⟩
        have hdis : ∀ j : Nat, j < nWords us → offs a i ≠ offs a (i + 1 + j) :=
          fun j _ => offs_ne a (by omega)
        refine ⟨g1, fun j w' hj hw => ?_, fun b v hb hl => ?_⟩
        · cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hw; subst hw
              simpa using g3 _ _ hdis hl1
          | succ j =>
              have := g2 j w' (by rw [nWords_one] at hj; omega) (by simpa using hw)
              rw [show i + 1 + j = i + (j + 1) by omega] at this; exact this
        · have hb0 : b ≠ offs a i := by have := hb 0 (by rw [nWords_one]; omega); simpa using this
          have hl' : Latest s1.mem s1.vs.coh b v := by
            show Latest mem' th.vs.coh b v
            rw [hmem]; exact Latest_push_other hl hb0 (by rw [hcoh]; simp [hb0, mth])
          exact g3 b v (fun j hj => by
            have := hb (j + 1) (by rw [nWords_one]; omega)
            rw [show i + (j + 1) = i + 1 + j by omega] at this; exact this) hl'
      · exfalso
        obtain ⟨_, hl⟩ := hn t htp
        exact hl m hm (by rw [hma]; rfl)
  | .two :: us, w0 :: w1 :: ws, i, s, V, hn, hV, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, _, q3, q4, q5⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      have hV0 : V ≤ max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel) :=
        Nat.le_trans hV (Nat.le_trans (storeMview_relSt (mth s pw w0 w1) _ [0] rel) (Nat.le_max_left _ _))
      have e0 : exprVal (mth s pw w0 w1) (dataE 1 w0) = w0.val :=
        exprVal_dataE _ 1 w0 (by simp [mth, regsOf])
      have e1 : exprVal (mth s pw w0 w1) (dataE 2 w1) = w1.val :=
        exprVal_dataE _ 2 w1 (by simp [mth, regsOf])
      rw [e0, e1] at q1
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q3 q4 q5 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q3 q4 q5 hs
      let s1 : St := { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises }
      have a01 : offs a i ≠ offs a (i + 1) := offs_ne a (by omega)
      have hn1 : NoProm s1 a.label := by
        have h1 := NoProm_push hn _ { s with mem := s.mem.push ⟨offs a i, w0.val,
          max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
            (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel)⟩ } rfl rfl
        exact NoProm_push h1 _ s1 (by show mem' = _; rw [q1]) (by show th.promises = _; rw [q4]; rfl)
      obtain ⟨g1, g2, g3⟩ := storeUnits_latest us ws (i + 2) s1 V hn1 (by show V ≤ th.vs.vRelSt; rw [q5]; exact hV) s' hs
      have hc : s1.vs.coh = fun b => if b = offs a i then s.mem.size
          else if b = offs a (i + 1) then s.mem.size + 1 else s.vs.coh b := by
        show th.vs.coh = _; rw [q3, offs_next]; rfl
      have hl0 : Latest s1.mem s1.vs.coh (offs a i) (bumpW V w0) := by
        show Latest mem' s1.vs.coh (offs a i) (bumpW V w0)
        rw [q1, offs_next]
        exact Latest_push_other (Latest_push_top (v := bumpW V w0) (by rw [hc]; simp) fun x g hx =>
          Nat.max_le.2 ⟨Nat.le_trans (storeMview_dataE _ 1 w0 (by simp [mth, regsOf]) [0] rel x g hx)
            (Nat.le_max_left _ _), hV0⟩) a01 rfl
      have hl1 : Latest s1.mem s1.vs.coh (offs a (i + 1)) (bumpW V w1) := by
        show Latest mem' s1.vs.coh (offs a (i + 1)) (bumpW V w1)
        rw [q1, offs_next]
        exact Latest_push_top (v := bumpW V w1) (by rw [hc]; simp [Ne.symm a01]) fun x g hx =>
          Nat.max_le.2 ⟨Nat.le_trans (storeMview_dataE _ 2 w1 (by simp [mth, regsOf]) [0] rel x g hx)
            (Nat.le_max_right _ _), hV0⟩
      refine ⟨g1, fun j w' hj hw => ?_, fun b v hb hl => ?_⟩
      · match j, hj, hw with
        | 0, _, hw =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hw; subst hw
            simpa using g3 _ _ (fun j _ => offs_ne a (by omega)) hl0
        | 1, _, hw =>
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw; subst hw
            exact g3 _ _ (fun j _ => offs_ne a (by omega)) hl1
        | j + 2, hj, hw =>
            have := g2 j w' (by rw [nWords_two] at hj; omega) (by simpa using hw)
            rw [show i + 2 + j = i + (j + 2) by omega] at this; exact this
      · have hb0 : b ≠ offs a i := by have := hb 0 (by rw [nWords_two]; omega); simpa using this
        have hb1 : b ≠ offs a (i + 1) := hb 1 (by rw [nWords_two]; omega)
        have hl' : Latest s1.mem s1.vs.coh b v := by
          show Latest mem' s1.vs.coh b v
          rw [q1, offs_next]
          exact Latest_push_other (Latest_push_other (coh' := s1.vs.coh) hl hb0 (by rw [hc]; simp [hb0, hb1])) hb1
            rfl
        exact g3 b v (fun j hj => by
          have := hb (j + 2) (by rw [nWords_two]; omega)
          rw [show i + (j + 2) = i + 2 + j by omega] at this; exact this) hl'
  | .one :: _, [], _, _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, _, _, s', hs => by simp [storeUnits] at hs

/-! ## §5 Whole own cells -/

theorem getElem?_map_val {ws : List Word} {o : Nat} {v : Val} (h : (ws.map (·.val))[o]? = some v) :
    ∃ w, ws[o]? = some w ∧ w.val = v := by
  rw [List.getElem?_map] at h
  cases hw : ws[o]? with
  | none => simp [hw] at h
  | some w => simp only [hw, Option.map_some, Option.some.injEq] at h; exact ⟨w, rfl, h⟩

/-- **Loading an own cell** returns a value of its type (the latest words), and
changes neither memory nor coherence. -/
theorem OwnOK_load {arch : Arch} {pw : Word} {acq : Bool} {η : TEnv} {l : AllocLabel} {c : Cell}
    {us : List Acc} {s : St} (ho : OwnOK η s.mem s.vs) (hc : η.sto l = some c)
    (hown : c.owner = some η.tid) (hus : wc c.ty = some (nWords us)) :
    ∃ vals, ValOf η c.ty vals ∧ ∀ r, r ∈ loadUnits arch pw ⟨l, 0⟩ acq us 0 s →
      WLe vals r.2 ∧ r.1.vs.coh = s.vs.coh ∧ r.1.mem = s.mem := by
  obtain ⟨vals, h1, h3, h4⟩ := OwnOK_plain ho hc hown (notArr_of_wc hus)
  rw [hus, Option.some.injEq] at h1
  exact ⟨vals, h3, loadUnits_latest us 0 s vals h1.symm (fun j v hj => by simpa [offs] using h4 j v hj)⟩

/-- **Storing a whole value to an own cell** keeps both invariants, provided
the thread has no outstanding promise there. -/
theorem OwnOK_store {k : Promises.Knobs} {arch : Arch} {pw : Word} {rel : Bool} {η : TEnv}
    {l : AllocLabel} {c : Cell} {us : List Acc} {ws : List Word}
    (hc : η.sto l = some c) (hus : wc c.ty = some (nWords us))
    {V : Ts} (hv : ValOf η c.ty (ws.map (bumpW V))) (hlen : ws.length = nWords us)
    {s : St} (hV : V ≤ s.vs.vRelSt) (hn : NoProm s l) (hm : MemOK η s.mem s.pairs) (ho : OwnOK η s.mem s.vs) :
    ∀ s', s' ∈ storeUnits k arch pw ⟨l, 0⟩ rel us ws 0 s →
      MemOK η s'.mem s'.pairs ∧ OwnOK η s'.mem s'.vs ∧ NoProm s' l := by
  intro s' hs
  have hm' := storeUnits_memOK (a := ⟨l, 0⟩) (b := 0) (o0 := 0) hc
    (Or.inl ⟨rfl, rfl, by obtain ⟨_, h, -⟩ := wc_some hus; simp [h]⟩) rfl
    ⟨hv, ShapeC_of_wc hus (by rw [List.length_map]; exact hlen)⟩ us ws 0 s
    (fun j w hw => ⟨bumpW V w, by simp [hw], WLe1_refl _⟩) hV hm s' hs
  obtain ⟨g1, g2, g3⟩ := storeUnits_latest (a := ⟨l, 0⟩) us ws 0 s V hn hV s' hs
  refine ⟨hm', fun l' c' hc' hown' => ?_, g1⟩
  by_cases hl : l' = l
  · subst hl; rw [hc] at hc'; cases hc'
    refine ⟨ws.map (bumpW V), Or.inl ⟨by rw [hus, List.length_map, hlen], hv⟩, fun o w' hw' => ?_⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w, ws[o]? = some w ∧ bumpW V w = w' := by
      rw [List.getElem?_map] at hw'
      cases h : ws[o]? with
      | none => simp [h] at hw'
      | some w => simp only [h, Option.map_some, Option.some.injEq] at hw'; exact ⟨w, rfl, hw'⟩
    have hlt : o < nWords us := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hw).1
    simpa [offs] using g2 o w hlt hw
  · obtain ⟨vals', h1, h4⟩ := ho l' c' hc' hown'
    refine ⟨vals', h1, fun o v hov => g3 _ _ (fun j _ => ?_) (h4 o v hov)⟩
    intro e; apply hl
    have := congrArg WeakMem.Address.label e
    simpa [offs] using this

/-! ## §6 Allocation -/

theorem fold_size (f : Nat → Msg) : ∀ (n : Nat) (M : Memory),
    ((List.range n).foldl (fun m j => m.push (f j)) M).size = M.size + n
  | 0, M => by simp
  | n + 1, M => by
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Array.size_push, fold_size f n M]
      omega

theorem fold_get (f : Nat → Msg) : ∀ (n : Nat) (M : Memory) (t : Nat),
    ((List.range n).foldl (fun m j => m.push (f j)) M)[t]? =
      if t < M.size then M[t]? else if t < M.size + n then some (f (t - M.size)) else none
  | 0, M, t => by
      simp only [List.range_zero, List.foldl_nil]
      by_cases h : t < M.size
      · simp [h]
      · simp [h]
  | n + 1, M, t => by
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [Array.getElem?_push, fold_get f n M t, fold_size]
      by_cases h1 : t = M.size + n
      · subst h1
        have h2 : ¬ M.size + n < M.size + n := Nat.lt_irrefl _
        by_cases h0 : n = 0
        · subst h0; simp
        · have h3 : ¬ M.size + n < M.size := by omega
          simp [h3]
      · by_cases h0 : t < M.size
        · simp [h1, h0]
        · have e : (t < M.size + n) ↔ (t < M.size + (n + 1)) := by omega
          simp only [h1, h0, ite_false]
          by_cases h4 : t < M.size + n
          · simp [h4, e.1 h4]
          · simp [h4, show ¬ t < M.size + (n + 1) from fun h => h4 (e.2 h)]

/-- Σ with a new own cell of type `T` at label `lbl`. -/
def allocE (η : TEnv) (lbl : AllocLabel) (T : Ty) : TEnv :=
  { η with sto := fun l => if l = lbl then some ⟨T, some η.tid⟩ else η.sto l }

theorem allocE_ne {η : TEnv} {lbl l : AllocLabel} {T : Ty} (h : l ≠ lbl) :
    (allocE η lbl T).sto l = η.sto l := by simp [allocE, h]
theorem allocE_eq {η : TEnv} {lbl : AllocLabel} {T : Ty} :
    (allocE η lbl T).sto lbl = some ⟨T, some η.tid⟩ := by simp [allocE]
theorem allocE_sub {η : TEnv} {lbl : AllocLabel} {T : Ty} (hnone : η.sto lbl = none)
    {l : AllocLabel} {c : Cell} (h : η.sto l = some c) : (allocE η lbl T).sto l = some c := by
  have hl : l ≠ lbl := by intro e; subst e; rw [hnone] at h; cases h
  rw [allocE_ne hl]; exact h

/-- **Allocation** (`new`, T3c-4): at a fresh label, with the stored words a
value of `T`, memory stays OK and the new cell is the thread's own, at its
latest words; the other own cells are untouched. -/
theorem alloc_ok {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} {η : TEnv} {T : Ty} (hus : wc T = some (nWords us)) (hlen : ws.length = nWords us)
    (hv : ValOf (allocE η lbl T) T (ws.map (bumpW s.vs.vRelSt)))
    (hfresh : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label ≠ lbl)
    (hnone : η.sto lbl = none) (hn : NoProm s lbl)
    (hm : MemOK η s.mem s.pairs) (ho : OwnOK η s.mem s.vs) :
    ∀ r, r ∈ alloc k arch lbl us ws s →
      MemOK (allocE η lbl T) r.1.mem r.1.pairs ∧ OwnOK (allocE η lbl T) r.1.mem r.1.vs ∧
      r.2 = cst (.loc ⟨lbl, 0⟩ 0) := by
  intro r hr
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  let n := nWords us
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩
  let M1 := (List.range n).foldl (fun m j => m.push (f j)) s.mem
  let V1 : VState := { s.vs with
    coh := fun b => if b.label = lbl ∧ b.offset < n then s.mem.size + b.offset else s.vs.coh b
    vWr := max s.vs.vWr (s.mem.size + n - 1) }
  let s1 : St := { s with mem := M1, vs := V1, nalloc := s.nalloc + 1 }
  have hs1 : s' ∈ storeUnits k arch (cst (.loc ⟨lbl, 0⟩ 0)) ⟨lbl, 0⟩ false us ws 0 s1 := hs
  have hget : ∀ t : Nat, M1[t]? =
      if t < s.mem.size then s.mem[t]? else if t < s.mem.size + n then some (f (t - s.mem.size)) else none :=
    fold_get f n s.mem
  have hsz : M1.size = s.mem.size + n := fold_size f n s.mem
  have hold : ∀ t : Nat, t < s.mem.size → M1[t]? = s.mem[t]? := fun t ht => by rw [hget t]; simp [ht]
  have hsub := fun {l} {c} (h : η.sto l = some c) => allocE_sub (T := T) hnone h
  have hmono : ∀ {U : Ty} {vs : List Word}, ValOf η U vs → ValOf (allocE η lbl T) U vs :=
    fun h => ValOf_mono (η₁ := η) (η₂ := allocE η lbl T) rfl rfl (fun _ _ h' => allocE_sub hnone h') (fun _ => Nat.le_refl _) h
  -- memory after the placeholders
  have hM1 : MemOK (allocE η lbl T) M1 s.pairs := by
    obtain ⟨h1, h2, h3⟩ := hm
    refine ⟨fun t m c ht hc => ?_, fun t m0 m1 c hp h0 h1' hc => ?_, fun t hp => ?_⟩
    · rw [hget t] at ht
      by_cases hlt : t < s.mem.size
      · simp only [hlt, ite_true] at ht
        have hne := hfresh t m ht
        rw [allocE_ne hne] at hc
        rcases h1 t m c ht hc with hu | hw
        · exact Or.inl hu
        · exact Or.inr (WordOK_map hmono hw)
      · simp only [hlt, ite_false] at ht
        split at ht
        · simp only [Option.some.injEq] at ht; subst ht; exact Or.inl rfl
        · cases ht
    · have hl := h3 t hp
      rw [hold t (Nat.lt_of_succ_lt hl)] at h0
      rw [hold (t + 1) hl] at h1'
      rw [allocE_ne (hfresh t m0 h0)] at hc
      exact PairOK_map hmono (h2 t m0 m1 c hp h0 h1' hc)
    · rw [hsz]; exact Nat.lt_of_lt_of_le (h3 t hp) (Nat.le_add_right _ _)
  have hn1 : NoProm s1 lbl := by
    intro t ht
    obtain ⟨hlt, hl⟩ := hn t ht
    refine ⟨by show t < M1.size; rw [hsz]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _),
      fun m hm' => hl m (by rw [← hold t hlt]; exact hm')⟩
  have hmem := storeUnits_memOK (a := ⟨lbl, 0⟩) (b := 0) (o0 := 0) (allocE_eq (η := η) (T := T))
    (Or.inl ⟨rfl, rfl, by obtain ⟨_, h, -⟩ := wc_some hus; simp [h]⟩) rfl ⟨hv, ShapeC_of_wc hus (by rw [List.length_map]; exact hlen)⟩ us ws 0 s1
    (fun j w hw => ⟨bumpW s.vs.vRelSt w, by simp [hw], WLe1_refl _⟩) (Nat.le_refl _) hM1 s' hs1
  obtain ⟨_, g2, g3⟩ := storeUnits_latest (a := ⟨lbl, 0⟩) us ws 0 s1 s.vs.vRelSt hn1 (Nat.le_refl _) s' hs1
  refine ⟨hmem, fun l' c' hc' hown' => ?_, rfl⟩
  by_cases hl : l' = lbl
  · subst hl
    rw [allocE_eq] at hc'; cases hc'
    refine ⟨ws.map (bumpW s.vs.vRelSt), Or.inl ⟨by rw [hus, List.length_map, hlen], hv⟩, fun o w' hw' => ?_⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w, ws[o]? = some w ∧ bumpW s.vs.vRelSt w = w' := by
      rw [List.getElem?_map] at hw'
      cases h : ws[o]? with
      | none => simp [h] at hw'
      | some w => simp only [h, Option.map_some, Option.some.injEq] at hw'; exact ⟨w, rfl, hw'⟩
    have hlt : o < nWords us := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hw).1
    simpa [offs] using g2 o w hlt hw
  · rw [allocE_ne hl] at hc'
    obtain ⟨vals', h1, h4⟩ := ho l' c' hc' hown'
    refine ⟨vals', CellOK_map hmono (Nat.le_refl _) h1, fun o v hov => g3 _ _ (fun j _ => ?_) ?_⟩
    · intro e; apply hl
      have := congrArg WeakMem.Address.label e
      simpa [offs] using this
    · -- the old latest survives the placeholders
      obtain ⟨⟨m, hm0, hma, hmv, hmw⟩, hab⟩ := h4 o v hov
      have hcoh : V1.coh ⟨l', o⟩ = s.vs.coh ⟨l', o⟩ := by simp [V1, hl]
      refine ⟨⟨m, ?_, hma, hmv, hmw⟩, fun t m' ht hm' => ?_⟩
      · show M1[V1.coh ⟨l', o⟩]? = some m
        rw [hcoh, hold _ (lt_of_get hm0)]; exact hm0
      · show m'.loc ≠ ⟨l', o⟩
        have ht' : s.vs.coh ⟨l', o⟩ < t := by rw [← hcoh]; exact ht
        change M1[t]? = some m' at hm'
        rw [hget t] at hm'
        by_cases hlt : t < s.mem.size
        · simp only [hlt, ite_true] at hm'
          exact hab t m' ht' hm'
        · simp only [hlt, ite_false] at hm'
          split at hm'
          · simp only [Option.some.injEq] at hm'; subst hm'
            intro e; apply hl
            have := congrArg WeakMem.Address.label e
            simpa [f, offs] using this.symm
          · cases hm'

/-- (T3c-5d) **An allocation, as its owner sees it**: each stored word is its
address's latest, every address at another label keeps its latest, and no
promise is at the new label. -/
theorem alloc_latest {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} (hn : NoProm s lbl) :
    ∀ r, r ∈ alloc k arch lbl us ws s →
      (∀ (j : Nat) w, j < nWords us → ws[j]? = some w →
        Latest r.1.mem r.1.vs.coh ⟨lbl, j⟩ (bumpW s.vs.vRelSt w)) ∧
      (∀ (b : Address) (v : Word), b.label ≠ lbl → Latest s.mem s.vs.coh b v → Latest r.1.mem r.1.vs.coh b v) ∧
      NoProm r.1 lbl := by
  intro r hr
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  let n := nWords us
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩
  let M1 := (List.range n).foldl (fun m j => m.push (f j)) s.mem
  let V1 : VState := { s.vs with
    coh := fun b => if b.label = lbl ∧ b.offset < n then s.mem.size + b.offset else s.vs.coh b
    vWr := max s.vs.vWr (s.mem.size + n - 1) }
  let s1 : St := { s with mem := M1, vs := V1, nalloc := s.nalloc + 1 }
  have hs1 : s' ∈ storeUnits k arch (cst (.loc ⟨lbl, 0⟩ 0)) ⟨lbl, 0⟩ false us ws 0 s1 := hs
  have hget : ∀ t : Nat, M1[t]? =
      if t < s.mem.size then s.mem[t]? else if t < s.mem.size + n then some (f (t - s.mem.size)) else none :=
    fold_get f n s.mem
  have hsz : M1.size = s.mem.size + n := fold_size f n s.mem
  have hold : ∀ t : Nat, t < s.mem.size → M1[t]? = s.mem[t]? := fun t ht => by rw [hget t]; simp [ht]
  have hn1 : NoProm s1 lbl := by
    intro t ht
    obtain ⟨hlt, hl⟩ := hn t ht
    refine ⟨by show t < M1.size; rw [hsz]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _),
      fun m hm' => hl m (by rw [← hold t hlt]; exact hm')⟩
  obtain ⟨g1, g2, g3⟩ := storeUnits_latest (a := ⟨lbl, 0⟩) us ws 0 s1 s.vs.vRelSt hn1 (Nat.le_refl _) s' hs1
  refine ⟨fun j w hj hw => by simpa [offs] using g2 j w hj hw, fun b v hl h4 => g3 _ _ (fun j _ => ?_) ?_, g1⟩
  · intro e; apply hl
    have := congrArg WeakMem.Address.label e
    simpa [offs] using this
  · obtain ⟨⟨m, hm0, hma, hmv, hmw⟩, hab⟩ := h4
    have hcoh : V1.coh b = s.vs.coh b := by simp [V1, hl]
    refine ⟨⟨m, ?_, hma, hmv, hmw⟩, fun t m' ht hm' => ?_⟩
    · show M1[V1.coh b]? = some m
      rw [hcoh, hold _ (lt_of_get hm0)]; exact hm0
    · show m'.loc ≠ b
      have ht' : s.vs.coh b < t := by rw [← hcoh]; exact ht
      change M1[t]? = some m' at hm'
      rw [hget t] at hm'
      by_cases hlt : t < s.mem.size
      · simp only [hlt, ite_true] at hm'
        exact hab t m' ht' hm'
      · simp only [hlt, ite_false] at hm'
        split at hm'
        · simp only [Option.some.injEq] at hm'; subst hm'
          intro e; apply hl
          have := congrArg WeakMem.Address.label e
          simpa [f, offs] using this.symm
        · cases hm'

/-- (T3c-5d) A store at a label outside Σ (a box's) keeps `MemOK`. -/
theorem storeUnits_memOK0 {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {η : TEnv} (hc : η.sto a.label = none) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St),
      MemOK η s.mem s.pairs → ∀ s', s' ∈ storeUnits k arch pw a rel us ws i s → MemOK η s'.mem s'.pairs
  | [], _, _, s, hm, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hm
  | .one :: us, w :: ws, i, s, hm, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, hcase, _, hrs⟩ := stepStore_cases hst
      have hm' : MemOK η mem' s.pairs := by
        rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · refine MemOK_push hm _ fun c' hc' => ?_
          simp only [offs] at hc'
          rw [hc] at hc'; cases hc'
        · exact hm
      exact storeUnits_memOK0 hc us ws (i + 1) _ hm' s' hs
  | .two :: us, w0 :: w1 :: ws, i, s, hm, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, q2, -, -, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel
      refine storeUnits_memOK0 hc us ws (i + 2) _ ?_ s' hs
      show MemOK η (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel).1
        (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel).2.1
      rw [q1, q2]
      refine MemOK_pushPair hm (offs a i) _ _ _ fun c' hc' => ?_
      simp only [offs] at hc'
      rw [hc] at hc'; cases hc'
  | .one :: _, [], _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, s', hs => by simp [storeUnits] at hs

/-- (T3c-5d) **An allocation outside Σ** (a box): Σ's invariants survive. -/
theorem alloc_ok0 {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} {η : TEnv} (hnone : η.sto lbl = none) (hn : NoProm s lbl)
    (hm : MemOK η s.mem s.pairs) (ho : OwnOK η s.mem s.vs) :
    ∀ r, r ∈ alloc k arch lbl us ws s →
      MemOK η r.1.mem r.1.pairs ∧ OwnOK η r.1.mem r.1.vs ∧ r.2 = cst (.loc ⟨lbl, 0⟩ 0) := by
  intro r hr
  have hL := (alloc_latest hn r hr).2.1
  refine ⟨?_, fun l c hc hown => ?_, ?_⟩
  rotate_left
  · obtain ⟨vals, h1, h2⟩ := ho l c hc hown
    have hl : l ≠ lbl := fun e => by rw [e, hnone] at hc; cases hc
    exact ⟨vals, h1, fun o v hv => hL ⟨l, o⟩ v hl (h2 o v hv)⟩
  · simp only [alloc, List.mem_map] at hr
    obtain ⟨s', hs, rfl⟩ := hr
    rfl
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  let n := nWords us
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩
  let M1 := (List.range n).foldl (fun m j => m.push (f j)) s.mem
  let V1 : VState := { s.vs with
    coh := fun b => if b.label = lbl ∧ b.offset < n then s.mem.size + b.offset else s.vs.coh b
    vWr := max s.vs.vWr (s.mem.size + n - 1) }
  let s1 : St := { s with mem := M1, vs := V1, nalloc := s.nalloc + 1 }
  have hs1 : s' ∈ storeUnits k arch (cst (.loc ⟨lbl, 0⟩ 0)) ⟨lbl, 0⟩ false us ws 0 s1 := hs
  have hget : ∀ t : Nat, M1[t]? =
      if t < s.mem.size then s.mem[t]? else if t < s.mem.size + n then some (f (t - s.mem.size)) else none :=
    fold_get f n s.mem
  have hsz : M1.size = s.mem.size + n := fold_size f n s.mem
  have hold : ∀ t : Nat, t < s.mem.size → M1[t]? = s.mem[t]? := fun t ht => by rw [hget t]; simp [ht]
  have hM1 : MemOK η M1 s.pairs := by
    obtain ⟨h1, h2, h3⟩ := hm
    refine ⟨fun t m c ht hc => ?_, fun t m0 m1 c hp h0 h1' hc => ?_, fun t hp => ?_⟩
    · rw [hget t] at ht
      by_cases hlt : t < s.mem.size
      · simp only [hlt, ite_true] at ht
        exact h1 t m c ht hc
      · simp only [hlt, ite_false] at ht
        split at ht
        · simp only [Option.some.injEq] at ht; subst ht; exact Or.inl rfl
        · cases ht
    · have hl := h3 t hp
      rw [hold t (Nat.lt_of_succ_lt hl)] at h0
      rw [hold (t + 1) hl] at h1'
      exact h2 t m0 m1 c hp h0 h1' hc
    · rw [hsz]; exact Nat.lt_of_lt_of_le (h3 t hp) (Nat.le_add_right _ _)
  exact storeUnits_memOK0 (a := ⟨lbl, 0⟩) hnone us ws 0 s1 hM1 s' hs1

/-! ## §7 What a store, a load or an allocation leaves alone (T3c-4d) -/

/-- Memory `M'` extends `M`, and every message past `M` is at label `l`. -/
def GrowsAt (M M' : Memory) (l : AllocLabel) : Prop :=
  M.size ≤ M'.size ∧ (∀ t, t < M.size → M'[t]? = M[t]?) ∧
    ∀ (t : Nat) (m : Msg), M.size ≤ t → M'[t]? = some m → m.loc.label = l

theorem GrowsAt_refl (M : Memory) (l : AllocLabel) : GrowsAt M M l :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ ht hm => absurd (lt_of_get hm) (by omega)⟩

theorem GrowsAt_trans {M1 M2 M3 : Memory} {l : AllocLabel} (h1 : GrowsAt M1 M2 l) (h2 : GrowsAt M2 M3 l) :
    GrowsAt M1 M3 l := by
  refine ⟨Nat.le_trans h1.1 h2.1, fun t ht => ?_, fun t m ht hm => ?_⟩
  · rw [h2.2.1 t (Nat.lt_of_lt_of_le ht h1.1), h1.2.1 t ht]
  · by_cases h : t < M2.size
    · rw [h2.2.1 t h] at hm; exact h1.2.2 t m ht hm
    · exact h2.2.2 t m (by omega) hm

theorem GrowsAt_push (M : Memory) (m : Msg) {l : AllocLabel} (hm : m.loc.label = l) : GrowsAt M (M.push m) l := by
  refine ⟨by simp, fun t ht => push_lt ht, fun t m' ht hm' => ?_⟩
  rw [Array.getElem?_push] at hm'
  by_cases e : t = M.size
  · rw [if_pos e, Option.some.injEq] at hm'; subst hm'; exact hm
  · rw [if_neg e] at hm'; exact absurd (lt_of_get hm') (by omega)

/-- `NoProm` survives growth when the promises are unchanged. -/
theorem NoProm_grows {s s' : St} {l l' : AllocLabel} (h : NoProm s l) (hp : s'.promises = s.promises)
    (hg : GrowsAt s.mem s'.mem l') : NoProm s' l := by
  intro t ht
  rw [hp] at ht
  obtain ⟨hlt, hl⟩ := h t ht
  exact ⟨Nat.lt_of_lt_of_le hlt hg.1, fun m hm => hl m (by rw [← hg.2.1 t hlt]; exact hm)⟩

/-- **A store with no promise at its cell** only appends, at that cell's label,
and changes neither the promises nor the allocation count. -/
theorem storeUnits_grows {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St), NoProm s a.label →
      ∀ s', s' ∈ storeUnits k arch pw a rel us ws i s →
        GrowsAt s.mem s'.mem a.label ∧ s'.promises = s.promises ∧ s'.nalloc = s.nalloc
  | [], _, _, s, _, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact ⟨GrowsAt_refl _ _, rfl, rfl⟩
  | .one :: us, w :: ws, i, s, hn, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, hcase, _⟩ := stepStore_cases hst
      rcases hcase with ⟨hmem, rfl, hprom⟩ | ⟨_, htp, m, hm, hma, _⟩
      · let s1 : St := { s with mem := mem', vs := th.vs, promises := th.promises }
        have hg1 : GrowsAt s.mem s1.mem a.label := by
          show GrowsAt s.mem mem' a.label; rw [hmem]; exact GrowsAt_push _ _ rfl
        have hp1 : s1.promises = s.promises := hprom
        obtain ⟨g1, g2, g3⟩ := storeUnits_grows us ws (i + 1) s1 (NoProm_grows hn hp1 hg1) s' hs
        exact ⟨GrowsAt_trans hg1 g1, g2.trans hp1, g3⟩
      · exfalso
        obtain ⟨_, hl⟩ := hn t htp
        exact hl m hm (by rw [hma]; rfl)
  | .two :: us, w0 :: w1 :: ws, i, s, hn, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, _, _, q4, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q4 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q4 hs
      let s1 : St := { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises }
      have hg1 : GrowsAt s.mem s1.mem a.label := by
        show GrowsAt s.mem mem' a.label
        rw [q1]; exact GrowsAt_trans (GrowsAt_push _ _ rfl) (GrowsAt_push _ _ rfl)
      have hp1 : s1.promises = s.promises := q4
      obtain ⟨g1, g2, g3⟩ := storeUnits_grows us ws (i + 2) s1 (NoProm_grows hn hp1 hg1) s' hs
      exact ⟨GrowsAt_trans hg1 g1, g2.trans hp1, g3⟩
  | .one :: _, [], _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, s', hs => by simp [storeUnits] at hs

/-- (D3) Loads leave the release view alone. -/
theorem stepLoad_relSt {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) : th'.vs.vRelSt = th.vs.vRelSt := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, _, rfl⟩ := h; rfl

theorem stepLoadPair_relSt {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th dst0 dst1 a deps acq) : th'.vs.vRelSt = th.vs.vRelSt := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, _, t1, _, hs⟩ := h
  split at hs
  · exact absurd hs (by simp)
  · simp only [Option.some.injEq] at hs; subst hs; rfl

theorem loadUnits_relSt {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.vs.vRelSt = s.vs.vRelSt
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; rfl
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact (loadUnits_relSt us (k + 1) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] }
        (s', ws) hmem).trans (stepLoad_relSt hth)
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact (loadUnits_relSt us (k + 2) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] }
        (s', ws) hmem).trans (stepLoadPair_relSt hth)

/-- (D3) Stores leave the release view alone. -/
theorem storeUnits_relSt {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St) (s' : St),
      s' ∈ storeUnits k arch pw a rel us ws i s → s'.vs.vRelSt = s.vs.vRelSt
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; rfl
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨_, _, _, hrs⟩ := stepStore_cases hst
      exact (storeUnits_relSt us ws (i + 1) _ s' hs).trans hrs
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨-, -, -, -, q5⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      exact (storeUnits_relSt us ws (i + 2) _ s' hs).trans q5
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

/-- (D3) Allocation leaves the release view alone. -/
theorem alloc_relSt {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} : ∀ r, r ∈ alloc k arch lbl us ws s → r.1.vs.vRelSt = s.vs.vRelSt := by
  intro r hr
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  have := storeUnits_relSt _ _ _ _ s' hs
  exact this

/-- (D3) Loads leave the write view alone. -/
theorem stepLoad_vWr {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) : th'.vs.vWr = th.vs.vWr := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, _, rfl⟩ := h; rfl

theorem stepLoadPair_vWr {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst0 dst1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th dst0 dst1 a deps acq) : th'.vs.vWr = th.vs.vWr := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, _, t1, _, hs⟩ := h
  split at hs
  · exact absurd hs (by simp)
  · simp only [Option.some.injEq] at hs; subst hs; rfl

theorem loadUnits_vWr {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.vs.vWr = s.vs.vWr
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; rfl
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact (loadUnits_vWr us (k + 1) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] }
        (s', ws) hmem).trans (stepLoad_vWr hth)
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact (loadUnits_vWr us (k + 2) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] }
        (s', ws) hmem).trans (stepLoadPair_vWr hth)

/-- (D3) A store's timestamp, and what it does to `vWr`. -/
theorem stepStore_vWr {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    ∃ t, ((mem' = mem.push ⟨a, exprVal th e, Promises.storeMview th e deps rel⟩ ∧ t = mem.size ∧
            th'.promises = th.promises) ∨
          (t ∈ th.promises ∧ ∃ m, mem[t]? = some m ∧ m.loc = a)) ∧
      th'.vs.vWr = max th.vs.vWr t := by
  cases e with
  | const c =>
      simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
      rcases h with h | ⟨t, htp, hf⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨mem.size, Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩
      · cases hm : mem[t]? with
        | none => simp [hm] at hf
        | some m =>
            simp only [hm] at hf
            split at hf
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
              exact ⟨t, Or.inr ⟨htp, m, hm, hcond.1.1.1⟩, rfl⟩
            · simp at hf
  | reg r =>
      simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
      rcases h with h | ⟨t, htp, hf⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨mem.size, Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩
      · cases hm : mem[t]? with
        | none => simp [hm] at hf
        | some m =>
            simp only [hm] at hf
            split at hf
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
              exact ⟨t, Or.inr ⟨htp, m, hm, hcond.1.1.1⟩, rfl⟩
            · simp at hf

theorem stepStorePair_vWr (mem : Memory) (pairs : List Ts) (th : Promises.Thread) (a : Address)
    (e0 e1 : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs.vWr = max th.vs.vWr (mem.size + 1) := by
  cases e0 <;> cases e1 <;> rfl

/-- (D3) **A store with no promise at its cell writes every word**: each at a
new timestamp, covered by the new `vWr`, which only grows. -/
theorem storeUnits_wr {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St), NoProm s a.label →
      ∀ s', s' ∈ storeUnits k arch pw a rel us ws i s →
        s.vs.vWr ≤ s'.vs.vWr ∧ ∀ j, j < nWords us → ∃ (t : Nat) (m : Msg), s.mem.size ≤ t ∧ t ≤ s'.vs.vWr ∧
          s'.mem[t]? = some m ∧ m.loc = offs a (i + j)
  | [], _, _, s, _, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      exact ⟨Nat.le_refl _, fun j hj => absurd hj (by simp [nWords])⟩
  | .one :: us, w :: ws, i, s, hn, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, hcase, hwr⟩ := stepStore_vWr hst
      rcases hcase with ⟨hmem, rfl, hprom⟩ | ⟨htp, m, hm, hma⟩
      · let s1 : St := { s with mem := mem', vs := th.vs, promises := th.promises }
        have hg1 : GrowsAt s.mem s1.mem a.label := by
          show GrowsAt s.mem mem' a.label; rw [hmem]; exact GrowsAt_push _ _ rfl
        have hp1 : s1.promises = s.promises := hprom
        have hn1 := NoProm_grows hn hp1 hg1
        obtain ⟨g1, g2⟩ := storeUnits_wr us ws (i + 1) s1 hn1 s' hs
        obtain ⟨gg, -, -⟩ := storeUnits_grows us ws (i + 1) s1 hn1 s' hs
        have hw1 : s.mem.size ≤ s1.vs.vWr := by
          show s.mem.size ≤ th.vs.vWr; rw [hwr]; exact Nat.le_max_right _ _
        have hsz : mem'.size = s.mem.size + 1 := by rw [hmem]; simp
        refine ⟨Nat.le_trans (by show s.vs.vWr ≤ th.vs.vWr; rw [hwr]; exact Nat.le_max_left _ _) g1,
          fun j hj => ?_⟩
        rcases j with _ | j
        · have e3 : s'.mem[s.mem.size]? = mem'[s.mem.size]? :=
            gg.2.1 _ (by show s.mem.size < mem'.size; omega)
          rw [hmem, Array.getElem?_push_size] at e3
          exact ⟨_, _, Nat.le_refl _, Nat.le_trans hw1 g1, e3, by simp [offs]⟩
        · obtain ⟨t, m, h1, h2, h3, h4⟩ := g2 j (by simp [nWords, Acc.size] at hj ⊢; omega)
          refine ⟨t, m, Nat.le_trans (by show s.mem.size ≤ mem'.size; omega) h1, h2, h3, ?_⟩
          rw [h4, show i + 1 + j = i + (j + 1) by omega]
      · exfalso
        obtain ⟨_, hl⟩ := hn t htp
        exact hl m hm (by rw [hma]; rfl)
  | .two :: us, w0 :: w1 :: ws, i, s, hn, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, _, _, q4, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      have q6 := stepStorePair_vWr s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q4 q6 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q4 q6 hs
      let s1 : St := { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises }
      have hg1 : GrowsAt s.mem s1.mem a.label := by
        show GrowsAt s.mem mem' a.label
        rw [q1]; exact GrowsAt_trans (GrowsAt_push _ _ rfl) (GrowsAt_push _ _ rfl)
      have hp1 : s1.promises = s.promises := q4
      have hn1 := NoProm_grows hn hp1 hg1
      obtain ⟨g1, g2⟩ := storeUnits_wr us ws (i + 2) s1 hn1 s' hs
      obtain ⟨gg, -, -⟩ := storeUnits_grows us ws (i + 2) s1 hn1 s' hs
      have hw1 : s.mem.size + 1 ≤ s1.vs.vWr := by
        show s.mem.size + 1 ≤ th.vs.vWr; rw [q6]; exact Nat.le_max_right _ _
      have hsz : mem'.size = s.mem.size + 2 := by rw [q1]; simp
      refine ⟨Nat.le_trans (by show s.vs.vWr ≤ th.vs.vWr; rw [q6]; exact Nat.le_max_left _ _) g1,
        fun j hj => ?_⟩
      rcases j with _ | _ | j
      · have e3 : s'.mem[s.mem.size]? = mem'[s.mem.size]? :=
          gg.2.1 _ (by show s.mem.size < mem'.size; omega)
        rw [q1] at e3
        simp only [Array.getElem?_push, Array.size_push] at e3
        simp only [show ¬ (s.mem.size = s.mem.size + 1) by omega, if_false, if_true] at e3
        exact ⟨_, _, Nat.le_refl _, Nat.le_trans (Nat.le_succ _) (Nat.le_trans hw1 g1), e3, by simp [offs]⟩
      · have e3 : s'.mem[s.mem.size + 1]? = mem'[s.mem.size + 1]? :=
          gg.2.1 _ (by show s.mem.size + 1 < mem'.size; omega)
        rw [q1] at e3
        simp only [Array.getElem?_push, Array.size_push, if_true] at e3
        exact ⟨_, _, Nat.le_succ _, Nat.le_trans hw1 g1, e3,
          by simp [offs, WeakMem.Address.next, Nat.add_assoc]⟩
      · obtain ⟨t, m, h1, h2, h3, h4⟩ := g2 j (by simp [nWords, Acc.size] at hj ⊢; omega)
        refine ⟨t, m, Nat.le_trans (by show s.mem.size ≤ mem'.size; omega) h1, h2, h3, ?_⟩
        rw [h4, show i + 2 + j = i + (j + 1 + 1) by omega]
  | .one :: _, [], _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, s', hs => by simp [storeUnits] at hs

/-- (D3) **Every message a store appends is a word of the stored value**
(`storeUnits_memOK` only says it is that or `undef`). -/
theorem storeUnits_newOK {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {η : TEnv} {c : Cell} {b o0 : Nat} {S : Ty} {vals : List Word} {V : Ts} (hc : η.sto a.label = some c)
    (hseg : SegOf c.ty b S) (hbo : a.offset = b + o0) (hv : ValOfS η S vals) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St),
      (∀ (j : Nat) w, ws[j]? = some w → ∃ w0, vals[o0 + i + j]? = some w0 ∧ WLe1 w0 (bumpW V w)) →
      V ≤ s.vs.vRelSt → NoProm s a.label →
      ∀ s', s' ∈ storeUnits k arch pw a rel us ws i s →
        ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
          m.loc.label = a.label ∧ WordOK η c.ty m.loc.offset (mw m)
  | [], _, _, s, _, _, _, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      intro t m ht hm; exact absurd (lt_of_get hm) (by omega)
  | .one :: us, w :: ws, i, s, hw, hV, hn, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t0, hcase, hwr⟩ := stepStore_vWr hst
      obtain ⟨_, _, _, hrs⟩ := stepStore_cases hst
      rcases hcase with ⟨hmem, rfl, hprom⟩ | ⟨htp, m, hm, hma⟩
      · let s1 : St := { s with mem := mem', vs := th.vs, promises := th.promises }
        have hg1 : GrowsAt s.mem s1.mem a.label := by
          show GrowsAt s.mem mem' a.label; rw [hmem]; exact GrowsAt_push _ _ rfl
        have hp1 : s1.promises = s.promises := hprom
        have hn1 := NoProm_grows hn hp1 hg1
        obtain ⟨gg, -, -⟩ := storeUnits_grows us ws (i + 1) s1 hn1 s' hs
        have ih := storeUnits_newOK hc hseg hbo hv us ws (i + 1) s1
          (fun j w' hj => by
            have := hw (j + 1) w' (by simpa using hj)
            rw [add_shift1]; exact this)
          (by show V ≤ th.vs.vRelSt; rw [hrs]; exact hV) hn1 s' hs
        have hsz : mem'.size = s.mem.size + 1 := by rw [hmem]; simp
        intro t m ht hm
        by_cases e : t = s.mem.size
        · subst e
          have e3 : s'.mem[s.mem.size]? = mem'[s.mem.size]? :=
            gg.2.1 _ (by show s.mem.size < mem'.size; omega)
          rw [hmem, Array.getElem?_push_size, hm, Option.some.injEq] at e3
          subst e3
          refine ⟨rfl, ?_⟩
          obtain ⟨w0, hw0, hle⟩ := hw 0 w rfl
          refine ⟨b, S, vals, o0 + i, w0, hseg, hv, by simpa using hw0, ?_, by simp only [offs]; rw [hbo, Nat.add_assoc]⟩
          show WLe1 w0 ⟨exprVal _ (dataE 1 w), Promises.storeMview _ (dataE 1 w) [0] rel, 0⟩
          rw [exprVal_dataE _ 1 w (by simp [mth, regsOf])]
          exact WLe1_msgB hle (storeMview_dataE _ 1 w (by simp [mth, regsOf]) [0] rel)
            (Nat.le_trans hV (storeMview_relSt (mth s pw w w) _ [0] rel))
        · exact ih t m (by show mem'.size ≤ t; omega) hm
      · exfalso
        obtain ⟨_, hl⟩ := hn t0 htp
        exact hl m hm (by rw [hma]; rfl)
  | .two :: us, w0 :: w1 :: ws, i, s, hw, hV, hn, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨x0, h0, l0⟩ := hw 0 w0 rfl
      obtain ⟨x1, h1, l1⟩ := hw 1 w1 rfl
      simp only [Nat.add_zero] at h0
      have e0 : exprVal (mth s pw w0 w1) (dataE 1 w0) = w0.val :=
        exprVal_dataE _ 1 w0 (by simp [mth, regsOf])
      have e1 : exprVal (mth s pw w0 w1) (dataE 2 w1) = w1.val :=
        exprVal_dataE _ 2 w1 (by simp [mth, regsOf])
      have hV0 : V ≤ max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel) :=
        Nat.le_trans hV (Nat.le_trans (storeMview_relSt (mth s pw w0 w1) _ [0] rel) (Nat.le_max_left _ _))
      have hok0 : WordOK η c.ty (offs a i).offset ⟨w0.val, max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel), 0⟩ :=
        ⟨b, S, vals, o0 + i, x0, hseg, hv, h0, WLe1_msgB l0 (fun x g hx =>
          Nat.le_trans (storeMview_dataE _ 1 w0 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_left _ _)) hV0,
          by simp only [offs]; rw [hbo, Nat.add_assoc]⟩
      have hok1 : WordOK η c.ty (offs a i).offset.succ ⟨w1.val, max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel), 0⟩ :=
        ⟨b, S, vals, o0 + i + 1, x1, hseg, hv, h1, WLe1_msgB l1 (fun x g hx =>
          Nat.le_trans (storeMview_dataE _ 2 w1 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_right _ _)) hV0,
          by simp only [offs]; rw [hbo]; omega⟩
      obtain ⟨q1, _, _, q4, q5⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q4 q5 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q4 q5 hs
      rw [e0, e1] at q1
      let s1 : St := { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises }
      have hg1 : GrowsAt s.mem s1.mem a.label := by
        show GrowsAt s.mem mem' a.label
        rw [q1]; exact GrowsAt_trans (GrowsAt_push _ _ rfl) (GrowsAt_push _ _ rfl)
      have hp1 : s1.promises = s.promises := q4
      have hn1 := NoProm_grows hn hp1 hg1
      obtain ⟨gg, -, -⟩ := storeUnits_grows us ws (i + 2) s1 hn1 s' hs
      have ih := storeUnits_newOK hc hseg hbo hv us ws (i + 2) s1
          (fun j w' hj => by
            have := hw (j + 2) w' (by simpa using hj)
            rw [add_shift2]; exact this)
          (by show V ≤ th.vs.vRelSt; rw [q5]; exact hV) hn1 s' hs
      have hsz : mem'.size = s.mem.size + 2 := by rw [q1]; simp
      intro t m ht hm
      by_cases e : t < s.mem.size + 2
      · have e3 : s'.mem[t]? = mem'[t]? := gg.2.1 _ (by show t < mem'.size; omega)
        rw [hm, q1] at e3
        by_cases e' : t = s.mem.size
        · subst e'
          simp only [Array.getElem?_push, Array.size_push,
            show ¬ (s.mem.size = s.mem.size + 1) by omega, if_false, if_true, Option.some.injEq] at e3
          subst e3
          exact ⟨rfl, hok0⟩
        · have e'' : t = s.mem.size + 1 := by omega
          subst e''
          simp only [Array.getElem?_push, Array.size_push, if_true, Option.some.injEq] at e3
          subst e3
          exact ⟨rfl, hok1⟩
      · exact ih t m (by show mem'.size ≤ t; omega) hm
  | .one :: _, [], _, _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, _, _, s', hs => by simp [storeUnits] at hs

/-- (M2b) `Hidden` survives growth of the environment, the bound, and memory,
when what is appended at `⟨l, o⟩` is a word of a value. -/
theorem Hidden_grow {η η' : TEnv} {T : Ty} {mem mem' : Memory} {l : AllocLabel} {o : Nat} {V V' : Ts}
    (h : Hidden η T mem l o V) (hw : ∀ w, WordOK η T o w → WordOK η' T o w) (hV : V ≤ V')
    (hold : ∀ t, t < mem.size → mem'[t]? = mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → m.loc = ⟨l, o⟩ →
      WordOK η' T o (mw m)) :
    Hidden η' T mem' l o V' := by
  intro t m ht hl hn
  by_cases hlt : t < mem.size
  · rw [hold t hlt] at ht
    obtain ⟨t', m', h1, h2, h3, h4⟩ := h t m ht hl (fun hw' => hn (hw _ hw'))
    exact ⟨t', m', h1, Nat.le_trans h2 hV, by rw [hold t' (lt_of_get h3)]; exact h3, h4⟩
  · exact absurd (hnew t m (by omega) ht hl) hn

/-- (M2b) **A store hides every placeholder of the words it writes**: below
the new `vWr`, by its own messages, which are words of the value. -/
theorem storeUnits_hid {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {η : TEnv} {c : Cell} {b o0 : Nat} {S : Ty} {vals : List Word} {V : Ts} (hc : η.sto a.label = some c)
    (hseg : SegOf c.ty b S) (hbo : a.offset = b + o0) (hv : ValOfS η S vals)
    (us : List Acc) (ws : List Word) (s : St)
    (hw : ∀ (j : Nat) w, ws[j]? = some w → ∃ w0, vals[o0 + 0 + j]? = some w0 ∧ WLe1 w0 (bumpW V w))
    (hV : V ≤ s.vs.vRelSt) (hn : NoProm s a.label) (s' : St) (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s) :
    ∀ j, j < nWords us → Hidden η c.ty s'.mem a.label (a.offset + j) s'.vs.vWr := by
  intro j hj t m ht hl hnw
  obtain ⟨_, g2⟩ := storeUnits_wr us ws 0 s hn s' hs
  have nk := storeUnits_newOK hc hseg hbo hv us ws 0 s hw hV hn s' hs
  by_cases hlt : s.mem.size ≤ t
  · obtain ⟨-, hok⟩ := nk t m hlt ht
    rw [hl] at hok; exact absurd hok hnw
  · obtain ⟨t', m', h1, h2, h3, h4⟩ := g2 j hj
    exact ⟨t', m', by omega, h2, h3, by rw [h4]; simp [offs]⟩

/-- (M2b) **A new cell's placeholders are hidden** below the `vWr` after its
initialising stores; `vWr` only grows. -/
theorem alloc_hid {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} {η : TEnv} {T : Ty}
    (hv : ValOf (allocE η lbl T) T (ws.map (bumpW s.vs.vRelSt))) (hsh : ShapeC T (ws.map (bumpW s.vs.vRelSt)))
    (hacc : accs T ≠ none) (hfresh : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label ≠ lbl) (hn : NoProm s lbl) :
    ∀ r, r ∈ alloc k arch lbl us ws s →
      s.vs.vWr ≤ r.1.vs.vWr ∧ ∀ o, Hidden (allocE η lbl T) T r.1.mem lbl o r.1.vs.vWr := by
  intro r hr
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  let n := nWords us
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩
  let M1 := (List.range n).foldl (fun m j => m.push (f j)) s.mem
  let V1 : VState := { s.vs with
    coh := fun b => if b.label = lbl ∧ b.offset < n then s.mem.size + b.offset else s.vs.coh b
    vWr := max s.vs.vWr (s.mem.size + n - 1) }
  let s1 : St := { s with mem := M1, vs := V1, nalloc := s.nalloc + 1 }
  have hs1 : s' ∈ storeUnits k arch (cst (.loc ⟨lbl, 0⟩ 0)) ⟨lbl, 0⟩ false us ws 0 s1 := hs
  have hget : ∀ t : Nat, M1[t]? =
      if t < s.mem.size then s.mem[t]? else if t < s.mem.size + n then some (f (t - s.mem.size)) else none :=
    fold_get f n s.mem
  have hsz : M1.size = s.mem.size + n := fold_size f n s.mem
  have hold : ∀ t : Nat, t < s.mem.size → M1[t]? = s.mem[t]? := fun t ht => by rw [hget t]; simp [ht]
  have hn1 : NoProm s1 lbl := by
    intro t ht
    obtain ⟨hlt, hl⟩ := hn t ht
    refine ⟨by show t < M1.size; rw [hsz]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _),
      fun m hm' => hl m (by rw [← hold t hlt]; exact hm')⟩
  obtain ⟨g1, g2⟩ := storeUnits_wr us ws 0 s1 hn1 s' hs1
  obtain ⟨gg, -, -⟩ := storeUnits_grows us ws 0 s1 hn1 s' hs1
  have nk := storeUnits_newOK (a := ⟨lbl, 0⟩) (b := 0) (o0 := 0) (allocE_eq (η := η) (T := T))
    (Or.inl ⟨rfl, rfl, hacc⟩) rfl ⟨hv, hsh⟩ us ws 0 s1
    (fun j w hw => ⟨bumpW s.vs.vRelSt w, by simp [hw], WLe1_refl _⟩) (Nat.le_refl _) hn1 s' hs1
  refine ⟨Nat.le_trans (Nat.le_max_left _ _) g1, fun o t m ht hl hnw => ?_⟩
  by_cases hlt : M1.size ≤ t
  · obtain ⟨-, hok⟩ := nk t m hlt ht
    rw [hl] at hok; exact absurd hok hnw
  · have ht1 : M1[t]? = some m := by rw [← gg.2.1 t (by show t < M1.size; omega)]; exact ht
    rw [hget t] at ht1
    by_cases hlt0 : t < s.mem.size
    · simp only [hlt0, ite_true] at ht1
      exact absurd (by rw [hl]) (hfresh t m ht1)
    · simp only [hlt0, ite_false] at ht1
      split at ht1
      · rename_i hlt2
        simp only [Option.some.injEq] at ht1; subst ht1
        have ho : o = t - s.mem.size := by
          have := congrArg WeakMem.Address.offset hl; simpa [f, offs] using this.symm
        obtain ⟨t', m', h1, h2, h3, h4⟩ := g2 o (by omega)
        exact ⟨t', m', by rw [hsz] at h1; omega, h2, h3, by rw [h4]; simp [offs]⟩
      · cases ht1

/-- **A load** changes only the view (and the `undef` count). -/
theorem loadUnits_frame {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.mem = s.mem ∧ r.1.pairs = s.pairs ∧ r.1.promises = s.promises ∧ r.1.nalloc = s.nalloc
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; exact ⟨rfl, rfl, rfl, rfl⟩
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, _, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_frame us (k + 1) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] } (s', ws) hmem
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, _, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_frame us (k + 2) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] } (s', ws) hmem

/-- **An allocation** with no promise at its label only appends there, keeps
the promises, and counts one more allocation. -/
theorem alloc_grows {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} (hn : NoProm s lbl) :
    ∀ r, r ∈ alloc k arch lbl us ws s →
      GrowsAt s.mem r.1.mem lbl ∧ r.1.promises = s.promises ∧ r.1.nalloc = s.nalloc + 1 := by
  intro r hr
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  let n := nWords us
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩
  let M1 := (List.range n).foldl (fun m j => m.push (f j)) s.mem
  let V1 : VState := { s.vs with
    coh := fun b => if b.label = lbl ∧ b.offset < n then s.mem.size + b.offset else s.vs.coh b
    vWr := max s.vs.vWr (s.mem.size + n - 1) }
  let s1 : St := { s with mem := M1, vs := V1, nalloc := s.nalloc + 1 }
  have hs1 : s' ∈ storeUnits k arch (cst (.loc ⟨lbl, 0⟩ 0)) ⟨lbl, 0⟩ false us ws 0 s1 := hs
  have hg1 : GrowsAt s.mem s1.mem lbl := by
    refine ⟨?_, fun t ht => ?_, fun t m ht hm => ?_⟩
    · show s.mem.size ≤ M1.size; rw [fold_size]; omega
    · show M1[t]? = s.mem[t]?; rw [fold_get]; simp [ht]
    · change M1[t]? = some m at hm
      rw [fold_get] at hm
      have h0 : ¬ t < s.mem.size := by omega
      simp only [h0, ite_false] at hm
      split at hm
      · simp only [Option.some.injEq] at hm; subst hm; rfl
      · cases hm
  obtain ⟨g1, g2, g3⟩ := storeUnits_grows (a := ⟨lbl, 0⟩) us ws 0 s1 (NoProm_grows hn rfl hg1) s' hs1
  exact ⟨GrowsAt_trans hg1 g1, g2, g3⟩

/-- **A store always has an outcome** when the words fill the units: appending
is always allowed. -/
theorem storeUnits_nonempty {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St), ws.length = nWords us →
      ∃ s', s' ∈ storeUnits k arch pw a rel us ws i s
  | [], _, _, s, _ => ⟨s, by simp [storeUnits]⟩
  | .one :: us, w :: ws, i, s, h => by
      have hx : ∃ x, x ∈ Promises.stepStore k arch s.mem (mth s pw w w) (offs a i) (dataE 1 w) [0] rel :=
        ⟨_, by unfold Promises.stepStore; exact List.mem_append_left _ (List.mem_singleton_self _)⟩
      obtain ⟨⟨mem', th⟩, hx⟩ := hx
      obtain ⟨s', hs'⟩ := storeUnits_nonempty (k := k) (arch := arch) (pw := pw) (a := a) (rel := rel)
        us ws (i + 1) { s with mem := mem', vs := th.vs, promises := th.promises }
        (by rw [nWords_one] at h; simp at h; omega)
      exact ⟨s', by simp only [storeUnits, List.mem_flatMap]; exact ⟨_, hx, hs'⟩⟩
  | .two :: us, w0 :: w1 :: ws, i, s, h => by
      simp only [storeUnits]
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R
      obtain ⟨mem', pairs', th⟩ := R
      exact storeUnits_nonempty us ws (i + 2) _ (by rw [nWords_two] at h; simp at h; omega)
  | .one :: us, [], _, _, h => by simp [nWords_one] at h
  | .two :: us, [], _, _, h => by simp [nWords_two] at h
  | .two :: us, [_], _, _, h => by simp [nWords_two] at h

/-! ### Load progress (T3c-4d-5): at latest addresses a load always has an outcome -/

/-- **The latest message is readable**, at any bound at or past coherence. -/
theorem readable_of_latest {mem : Memory} {coh : Address → Ts} {a : Address} {v : Word} (bound : Ts)
    (hl : Latest mem coh a v) : WeakMem.readable mem a (coh a) bound = true ∧ coh a < mem.size := by
  obtain ⟨⟨m, hm, hma, _⟩, hnone⟩ := hl
  refine ⟨?_, lt_of_get hm⟩
  have hh : WeakMem.hiddenFrom mem a (coh a) bound = false := by
    unfold WeakMem.hiddenFrom
    rw [Bool.eq_false_iff]
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨t', _, h⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlt, h⟩ := h
    cases ht : mem[t']? with
    | none => simp [ht] at h
    | some m' =>
        simp [ht] at h
        exact hnone t' m' hlt ht h
  simp [WeakMem.readable, hm, hma, hh]

/-- **A pair load at latest addresses cannot straddle**: a pair written to
`(a, a.next)` sits at or before both coherence points. -/
theorem noStraddle_latest {mem : Memory} {pairs : List Ts} {coh : Address → Ts} {a : Address}
    {v0 v1 : Word} (hl0 : Latest mem coh a v0) (hl1 : Latest mem coh a.next v1) :
    WeakMem.pairStraddles mem pairs a (coh a) (coh a.next) = false := by
  unfold WeakMem.pairStraddles
  rw [Bool.eq_false_iff]
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨p, _, h⟩ := h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have e0 : p ≤ coh a := by
    cases hp : mem[p]? with
    | none => simp [hp] at h0
    | some m =>
        simp [hp] at h0
        exact Nat.le_of_not_lt fun hlt => hl0.2 p m hlt hp h0
  have e1 : p + 1 ≤ coh a.next := by
    cases hp : mem[p + 1]? with
    | none => simp [hp] at h1
    | some m =>
        simp [hp] at h1
        exact Nat.le_of_not_lt fun hlt => hl1.2 (p + 1) m hlt hp h1
  simp [e0, e1] at h2

/-- **Loading latest words always succeeds** (progress for own loads). -/
theorem loadUnits_nonempty {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (vals : List Word), vals.length = nWords us →
      (∀ j v, vals[j]? = some v → Latest s.mem s.vs.coh (offs a (k + j)) v) →
      ∃ r, r ∈ loadUnits arch pw a acq us k s
  | [], k, s, _, _, _ => ⟨(s, []), by simp [loadUnits]⟩
  | .one :: us, k, s, vals, hn, hl => by
      cases vals with
      | nil => simp [nWords, Acc.size] at hn; omega
      | cons v rest =>
          have hl0 : Latest s.mem s.vs.coh (offs a k) v := by
            have := hl 0 v rfl; simpa using this
          obtain ⟨hr, hlt⟩ := readable_of_latest
            (Promises.readBoundOf arch s.vs (Promises.depBound (mth s pw pw pw).regs [0]) (offs a k)) hl0
          have hx : ∃ th, th ∈ Promises.stepLoad arch s.mem s.pairs (mth s pw pw pw) 1 (offs a k) [0] acq :=
            ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨List.mem_range.2 hlt, hr⟩)⟩
          obtain ⟨th, hth⟩ := hx
          obtain ⟨_, hc⟩ := stepLoad_latest (th := mth s pw pw pw) hl0 hth
          have hn' : rest.length = nWords us := by
            simp [nWords, Acc.size] at hn ⊢; omega
          obtain ⟨⟨s', ws⟩, hmem⟩ := loadUnits_nonempty (arch := arch) (pw := pw) (a := a) (acq := acq) us (k + 1)
            { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] } rest hn'
            (fun j v' hj => by
              have := hl (j + 1) v' (by simpa using hj)
              simp only [hc]
              rw [show k + 1 + j = k + (j + 1) by omega]
              exact this)
          exact ⟨_, by
            simp only [loadUnits, List.mem_flatMap, List.mem_map]
            exact ⟨th, hth, (s', ws), hmem, rfl⟩⟩
  | .two :: us, k, s, vals, hn, hl => by
      match vals, hn, hl with
      | [], hn, _ => simp [nWords, Acc.size] at hn; omega
      | [_], hn, _ => simp [nWords, Acc.size] at hn; omega
      | v0 :: v1 :: rest, hn, hl =>
          have hl0 : Latest s.mem s.vs.coh (offs a k) v0 := by
            have := hl 0 v0 rfl; simpa using this
          have hl1 : Latest s.mem s.vs.coh (offs a k).next v1 := by
            have := hl 1 v1 rfl
            have e : (offs a k).next = offs a (k + 1) := by simp [offs, WeakMem.Address.next, Nat.add_assoc]
            rw [e]; simpa using this
          let d := Promises.depBound (mth s pw pw pw).regs [0]
          obtain ⟨hr0, hlt0⟩ := readable_of_latest (Promises.readBoundOf arch s.vs d (offs a k)) hl0
          obtain ⟨hr1, hlt1⟩ := readable_of_latest (Promises.readBoundOf arch s.vs d (offs a k).next) hl1
          have hns := noStraddle_latest (pairs := s.pairs) hl0 hl1
          have hx : ∃ th, th ∈ Promises.stepLoadPair arch s.mem s.pairs (mth s pw pw pw) 1 2 (offs a k) [0] acq := by
            simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
              List.mem_range]
            exact ⟨_, _, ⟨hlt0, hr0⟩, _, ⟨hlt1, hr1⟩, by simp only [mth] at hns ⊢; rw [hns]; rfl⟩
          obtain ⟨th, hth⟩ := hx
          obtain ⟨_, _, hc⟩ := stepLoadPair_latest (th := mth s pw pw pw) (by decide) hl0 hl1 hth
          have hn' : rest.length = nWords us := by
            simp only [List.length_cons, nWords, List.map_cons, List.sum_cons, Acc.size] at hn ⊢; omega
          obtain ⟨⟨s', ws⟩, hmem⟩ := loadUnits_nonempty (arch := arch) (pw := pw) (a := a) (acq := acq) us (k + 2)
            { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] } rest hn'
            (fun j v' hj => by
              have := hl (j + 2) v' (by simpa using hj)
              simp only [hc]
              rw [show k + 2 + j = k + (j + 2) by omega]
              exact this)
          exact ⟨_, by
            simp only [loadUnits, List.mem_flatMap, List.mem_map]
            exact ⟨th, hth, (s', ws), hmem, rfl⟩⟩

/-- **An own cell can always be loaded.** -/
theorem OwnOK_load_nonempty {arch : Arch} {pw : Word} {acq : Bool} {η : TEnv} {l : AllocLabel} {c : Cell}
    {us : List Acc} {s : St} (ho : OwnOK η s.mem s.vs) (hc : η.sto l = some c)
    (hown : c.owner = some η.tid) (hus : wc c.ty = some (nWords us)) :
    ∃ r, r ∈ loadUnits arch pw ⟨l, 0⟩ acq us 0 s := by
  obtain ⟨vals, h1, _, h4⟩ := OwnOK_plain ho hc hown (notArr_of_wc hus)
  rw [hus, Option.some.injEq] at h1
  exact loadUnits_nonempty us 0 s vals h1.symm (fun j v hj => by simpa [offs] using h4 j v hj)

/-! ## §8 (T3c-7) Stores that may fulfil a promise

A one-word store may land on one of the thread's outstanding promises instead
of appending (`stepStore_cases`).  That leaves memory alone and only moves
coherence at the stored address, so a store to another thread's cell keeps the
thread's invariant whether or not it fulfils.  These are the promise-agnostic
forms of §7's facts. -/

/-- (T3c-7) A one-word store keeps or discharges promises, never adds one. -/
theorem stepStore_promSub {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    ∀ t, t ∈ th'.promises → t ∈ th.promises := by
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨t, htp, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun _ h => h
    · cases hm : mem[t]? with
      | none => simp [hm] at hf
      | some m =>
          simp only [hm] at hf
          split at hf
          · simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            exact fun _ h => List.mem_of_mem_erase h
          · simp at hf

/-- (T3c-7) `NoProm` survives growth when promises are only discharged. -/
theorem NoProm_growsP {s s' : St} {l l' : AllocLabel} (h : NoProm s l)
    (hp : ∀ t, t ∈ s'.promises → t ∈ s.promises) (hg : GrowsAt s.mem s'.mem l') : NoProm s' l := by
  intro t ht
  obtain ⟨hlt, hl⟩ := h t (hp t ht)
  exact ⟨Nat.lt_of_lt_of_le hlt hg.1, fun m hm => hl m (by rw [← hg.2.1 t hlt]; exact hm)⟩

/-- (T3c-7) **A store** only appends, at its cell's label, and only
discharges promises (`storeUnits_grows` without `NoProm`). -/
theorem storeUnits_growsF {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      GrowsAt s.mem s'.mem a.label ∧ (∀ t, t ∈ s'.promises → t ∈ s.promises) ∧ s'.nalloc = s.nalloc
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      exact ⟨GrowsAt_refl _ _, fun _ h => h, rfl⟩
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, hcase, _⟩ := stepStore_cases hst
      have hps := stepStore_promSub hst
      have hg1 : GrowsAt s.mem mem' a.label := by
        rcases hcase with ⟨hmem, -, -⟩ | ⟨hmem, -⟩
        · rw [hmem]; exact GrowsAt_push _ _ rfl
        · rw [hmem]; exact GrowsAt_refl _ _
      obtain ⟨g1, g2, g3⟩ := storeUnits_growsF us ws (i + 1) _ s' hs
      exact ⟨GrowsAt_trans hg1 g1, fun t ht => hps t (g2 t ht), g3⟩
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, _, _, q4, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q4 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q4 hs
      have hg1 : GrowsAt s.mem mem' a.label := by
        rw [q1]; exact GrowsAt_trans (GrowsAt_push _ _ rfl) (GrowsAt_push _ _ rfl)
      obtain ⟨g1, g2, g3⟩ := storeUnits_growsF us ws (i + 2) _ s' hs
      exact ⟨GrowsAt_trans hg1 g1, fun t ht => by have := g2 t ht; rw [q4] at this; exact this, g3⟩
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

/-- (T3c-7) A store only raises `vWr`. -/
theorem storeUnits_wrF {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      s.vs.vWr ≤ s'.vs.vWr
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact Nat.le_refl _
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, -, hwr⟩ := stepStore_vWr hst
      have g := storeUnits_wrF us ws (i + 1) _ s' hs
      exact Nat.le_trans (by show s.vs.vWr ≤ th.vs.vWr; rw [hwr]; exact Nat.le_max_left _ _) g
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      have q6 := stepStorePair_vWr s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q6 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q6 hs
      have g := storeUnits_wrF us ws (i + 2) _ s' hs
      exact Nat.le_trans (by show s.vs.vWr ≤ th.vs.vWr; rw [q6]; exact Nat.le_max_left _ _) g
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

/-- (T3c-7) A store leaves every address at another label at its latest. -/
theorem storeUnits_latestF {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ (b : Address) (v : Word), b.label ≠ a.label → Latest s.mem s.vs.coh b v → Latest s'.mem s'.vs.coh b v
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact fun _ _ _ h => h
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t, hcase, hcoh, -⟩ := stepStore_cases hst
      intro b v hbl hl
      have hb0 : b ≠ offs a i := fun e => hbl (by rw [e]; rfl)
      have hc : th.vs.coh b = s.vs.coh b := by rw [hcoh]; simp [hb0, mth]
      have hl1 : Latest mem' th.vs.coh b v := by
        rcases hcase with ⟨hmem, -, -⟩ | ⟨hmem, -⟩
        · rw [hmem]; exact Latest_push_other hl hb0 hc
        · rw [hmem]; unfold Latest; rw [hc]; exact hl
      exact storeUnits_latestF us ws (i + 1) _ s' hs b v hbl hl1
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨q1, _, q3, _, _⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q3 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q3 hs
      intro b v hbl hl
      have hb0 : b ≠ offs a i := fun e => hbl (by rw [e]; rfl)
      have hb1 : b ≠ (offs a i).next := fun e => hbl (by rw [e]; rfl)
      have hl1 : Latest mem' th.vs.coh b v := by
        rw [q1]
        exact Latest_push_other (Latest_push_other (coh' := th.vs.coh) hl hb0 (by rw [q3]; simp [hb0, hb1, mth]))
          hb1 rfl
      exact storeUnits_latestF us ws (i + 2) _ s' hs b v hbl hl1
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

/-- (T3c-7) **Every message a store appends is a word of the stored value**,
whether or not some units fulfil promises (`storeUnits_newOK` without `NoProm`). -/
theorem storeUnits_newOKF {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {η : TEnv} {c : Cell} {b o0 : Nat} {S : Ty} {vals : List Word} {V : Ts} (hc : η.sto a.label = some c)
    (hseg : SegOf c.ty b S) (hbo : a.offset = b + o0) (hv : ValOfS η S vals) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St),
      (∀ (j : Nat) w, ws[j]? = some w → ∃ w0, vals[o0 + i + j]? = some w0 ∧ WLe1 w0 (bumpW V w)) →
      V ≤ s.vs.vRelSt →
      ∀ s', s' ∈ storeUnits k arch pw a rel us ws i s →
        ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
          m.loc.label = a.label ∧ WordOK η c.ty m.loc.offset (mw m)
  | [], _, _, s, _, _, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      intro t m ht hm; exact absurd (lt_of_get hm) (by omega)
  | .one :: us, w :: ws, i, s, hw, hV, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨t0, hcase, _, hrs⟩ := stepStore_cases hst
      let s1 : St := { s with mem := mem', vs := th.vs, promises := th.promises }
      obtain ⟨gg, -, -⟩ := storeUnits_growsF us ws (i + 1) s1 s' hs
      have ih := storeUnits_newOKF hc hseg hbo hv us ws (i + 1) s1
        (fun j w' hj => by
          have := hw (j + 1) w' (by simpa using hj)
          rw [add_shift1]; exact this)
        (by show V ≤ th.vs.vRelSt; rw [hrs]; exact hV) s' hs
      rcases hcase with ⟨hmem, rfl, hprom⟩ | ⟨hmem, -⟩
      · have hsz : mem'.size = s.mem.size + 1 := by rw [hmem]; simp
        intro t m ht hm
        by_cases e : t = s.mem.size
        · subst e
          have e3 : s'.mem[s.mem.size]? = mem'[s.mem.size]? :=
            gg.2.1 _ (by show s.mem.size < mem'.size; omega)
          rw [hmem, Array.getElem?_push_size, hm, Option.some.injEq] at e3
          subst e3
          refine ⟨rfl, ?_⟩
          obtain ⟨w0, hw0, hle⟩ := hw 0 w rfl
          refine ⟨b, S, vals, o0 + i, w0, hseg, hv, by simpa using hw0, ?_, by simp only [offs]; rw [hbo, Nat.add_assoc]⟩
          show WLe1 w0 ⟨exprVal _ (dataE 1 w), Promises.storeMview _ (dataE 1 w) [0] rel, 0⟩
          rw [exprVal_dataE _ 1 w (by simp [mth, regsOf])]
          exact WLe1_msgB hle (storeMview_dataE _ 1 w (by simp [mth, regsOf]) [0] rel)
            (Nat.le_trans hV (storeMview_relSt (mth s pw w w) _ [0] rel))
        · exact ih t m (by show mem'.size ≤ t; omega) hm
      · intro t m ht hm
        exact ih t m (by show mem'.size ≤ t; rw [hmem]; exact ht) hm
  | .two :: us, w0 :: w1 :: ws, i, s, hw, hV, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨x0, h0, l0⟩ := hw 0 w0 rfl
      obtain ⟨x1, h1, l1⟩ := hw 1 w1 rfl
      simp only [Nat.add_zero] at h0
      have e0 : exprVal (mth s pw w0 w1) (dataE 1 w0) = w0.val :=
        exprVal_dataE _ 1 w0 (by simp [mth, regsOf])
      have e1 : exprVal (mth s pw w0 w1) (dataE 2 w1) = w1.val :=
        exprVal_dataE _ 2 w1 (by simp [mth, regsOf])
      have hV0 : V ≤ max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel) :=
        Nat.le_trans hV (Nat.le_trans (storeMview_relSt (mth s pw w0 w1) _ [0] rel) (Nat.le_max_left _ _))
      have hok0 : WordOK η c.ty (offs a i).offset ⟨w0.val, max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel), 0⟩ :=
        ⟨b, S, vals, o0 + i, x0, hseg, hv, h0, WLe1_msgB l0 (fun x g hx =>
          Nat.le_trans (storeMview_dataE _ 1 w0 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_left _ _)) hV0,
          by simp only [offs]; rw [hbo, Nat.add_assoc]⟩
      have hok1 : WordOK η c.ty (offs a i).offset.succ ⟨w1.val, max (Promises.storeMview (mth s pw w0 w1) (dataE 1 w0) [0] rel)
          (Promises.storeMview (mth s pw w0 w1) (dataE 2 w1) [0] rel), 0⟩ :=
        ⟨b, S, vals, o0 + i + 1, x1, hseg, hv, h1, WLe1_msgB l1 (fun x g hx =>
          Nat.le_trans (storeMview_dataE _ 2 w1 (by simp [mth, regsOf]) [0] rel x g hx) (Nat.le_max_right _ _)) hV0,
          by simp only [offs]; rw [hbo]; omega⟩
      obtain ⟨q1, _, _, q4, q5⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at q1 q4 q5 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q4 q5 hs
      rw [e0, e1] at q1
      let s1 : St := { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises }
      obtain ⟨gg, -, -⟩ := storeUnits_growsF us ws (i + 2) s1 s' hs
      have ih := storeUnits_newOKF hc hseg hbo hv us ws (i + 2) s1
          (fun j w' hj => by
            have := hw (j + 2) w' (by simpa using hj)
            rw [add_shift2]; exact this)
          (by show V ≤ th.vs.vRelSt; rw [q5]; exact hV) s' hs
      have hsz : mem'.size = s.mem.size + 2 := by rw [q1]; simp
      intro t m ht hm
      by_cases e : t < s.mem.size + 2
      · have e3 : s'.mem[t]? = mem'[t]? := gg.2.1 _ (by show t < mem'.size; omega)
        rw [hm, q1] at e3
        by_cases e' : t = s.mem.size
        · subst e'
          simp only [Array.getElem?_push, Array.size_push,
            show ¬ (s.mem.size = s.mem.size + 1) by omega, if_false, if_true, Option.some.injEq] at e3
          subst e3
          exact ⟨rfl, hok0⟩
        · have e'' : t = s.mem.size + 1 := by omega
          subst e''
          simp only [Array.getElem?_push, Array.size_push, if_true, Option.some.injEq] at e3
          subst e3
          exact ⟨rfl, hok1⟩
      · exact ih t m (by show mem'.size ≤ t; omega) hm
  | .one :: _, [], _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, _, s', hs => by simp [storeUnits] at hs

end TermMem

/-! ### (P4 step 2) Resourceful memory values -/

namespace TermSound
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv

/-- (D3) **Forgetting `seen`**, resourcefully: `VRR` survives dropping `seen` at
labels whose frontier is at most `V`, for words whose pointers all have view at
least `V`; the resources are unchanged. -/
theorem VRR_unsee (V : WeakMem.Ts) : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word)
    (X : Res),
    (∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S vs Y) → (∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S vs Y) →
    η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l ∨ ∃ f, η₁.pfr l = some f ∧ f ≤ V) →
    (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    LocAbove V ws → VRR ρ η₁ t rt ws X → (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) → VRR ρ η₂ t rt ws X
  | .tvar k, η₁, η₂, ρ, rt, ws, X, hr, hur, _, _, _, _, _, _, _, hBx, _, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ X h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      exact ⟨VRR_unsee V t η₁ η₂ ρ rt ws X hr hur hw hp ht hs hi hP hS hBx hL hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VRR_unsee V b η₁ η₂ (vcons w ρ) rb ws X hr hur hw hp ht hs hi hP hS hBx hL h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨ra, rb, h1, Ra, Rb, hR, hz, hf⟩ := hv
      refine ⟨ra, rb, h1, Ra, Rb, hR, hz, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VRR_unsee V a η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.take n) e2,
        VRR_unsee V b η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.drop n) e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, boxSeen_unsee hP hS hx hL hm,
          fun hj => ⟨fun e => VRR_unsee V a η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx hL ((hA hj).1 e),
            fun e => ?_⟩,
          fun hj => ⟨fun e => VRR_unsee V b η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx hL ((hA' hj).1 e),
            fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRR_mono a η₁.unsee η₂.unsee ρ _ _ _ hur hur hw hp ht hs hi hP
            (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRR_mono b η₁.unsee η₂.unsee ρ _ _ _ hur hur hw hp ht hs hi hP
            (fun _ h => h.elim) hBx hv⟩
      · have hLp := LocAbove_decodeArm hd hL
        refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          exact ⟨q, hq, VRR_unsee V a η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj
          exact ⟨q, hq, VRR_unsee V b η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hv⟩
  | .code a b, η₁, η₂, ρ, rt, ws, X, _, _, hw, hp, _, _, _, _, _, hBx, _, hv, hri => by
      simp only [VRR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VRR_unsee V b (η₁.push0 s) (η₂.push0 s) ρ rb ws X
        (push0_rrs_mono hr) (push0_urrs_mono hur) ?_ hp ht hs hi hP hS hBx hL h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, X, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      exact ⟨⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_unsee hP hS h1 hL h5, h6⟩, hR⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, X, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl hn, hR⟩
      · exact ⟨Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_unsee hP hS h1 hL h5, h6⟩, hR⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, X, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl ⟨hn.1, hw ▸ hn.2⟩, hR⟩
      · exact ⟨Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOK_unsee hP hS h1 hL h5,
          IniAt_mono (modeIni_le hi hri μ) h6⟩, hR⟩
  | .mu b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      rw [← hw]
      refine VRR_unsee V b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws X
        (push0_rrs_mono hr) (push0_urrs_mono hur) ?_ hp ht hs hi hP hS hBx hL hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VRR] at hv ⊢
      exact fun n => VRR_unsee V b η₁ η₂ (vcons n ρ) rt ws X hr hur hw hp ht hs hi hP hS hBx hL (hv n)
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simp [VRR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv

/-- (P3) **Copyable values exist resource-free.**  A non-affine type whose type
variables are bound below `ke.length`, read where every copy-kinded variable's
plain values are also its resource-free values, has every value as a value
carrying nothing. -/
theorem VR_VRR_copy : ∀ (t : Ty) (ke : KEnv) (ρ : Nat → Nat) (η : TEnv) (rt : Shp) (ws : List Word),
    Ty.affineIn ke t = false → tb ke.length t = true →
    (∀ k, k < ke.length → ke.ask k true (·.copy) = true → ∀ S vs, η.rels k S vs → η.rrs k S vs .zero) →
    (∀ k, k < ke.length → ke.ask k true (·.copy) = true → ∀ S vs, η.urels k S vs → η.urrs k S vs .zero) →
    VR ρ η t rt ws → VRR ρ η t rt ws .zero
  | .tvar k, ke, ρ, η, rt, ws, ha, htb, hr, _, hv => by
      simp only [Ty.affineIn, Bool.not_eq_false'] at ha
      simp only [tb, decide_eq_true_eq] at htb
      simp only [VR, TEnv.get] at hv; simp only [VRR]
      obtain ⟨w0, h0, h⟩ := hv
      exact ⟨w0, h0, hr k htb ha rt w0 h⟩
  | .refine t _, ke, ρ, η, rt, ws, ha, htb, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [tb] at htb; simp only [VR] at hv; simp only [VRR]
      exact ⟨VR_VRR_copy t ke ρ η rt ws ha htb hr hu hv.1, hv.2⟩
  | .iex b, ke, ρ, η, rt, ws, ha, htb, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [tb] at htb; simp only [VR] at hv; simp only [VRR]
      obtain ⟨n, rb, w, e, hv⟩ := hv
      exact ⟨n, rb, w, e, VR_VRR_copy b ke _ η rb ws ha htb hr hu hv⟩
  | .iall b, ke, ρ, η, rt, ws, ha, htb, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [tb] at htb; simp only [VR] at hv; simp only [VRR]
      exact fun n => VR_VRR_copy b ke _ η rt ws ha htb hr hu (hv n)
  | .prod a b, ke, ρ, η, rt, ws, ha, htb, hr, hu, hv => by
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at ha
      simp only [tb, Bool.and_eq_true] at htb
      simp only [VR] at hv; simp only [VRR]
      obtain ⟨ra, rb, e, hf⟩ := hv
      refine ⟨ra, rb, e, .zero, .zero, (Res.zero_add _).symm, fun _ => trivial, fun n hn => ?_⟩
      obtain ⟨h0, h1, h2⟩ := hf n hn
      exact ⟨h0, VR_VRR_copy a ke ρ η ra _ ha.1 htb.1 hr hu h1, VR_VRR_copy b ke ρ η rb _ ha.2 htb.2 hr hu h2⟩
  | .sum a b, ke, ρ, η, rt, ws, ha, htb, hr, hu, hv => by
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at ha
      simp only [tb, Bool.and_eq_true] at htb
      simp only [VR] at hv; simp only [VRR]
      obtain ⟨n, Ra, Rb, e, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · refine ⟨n, Ra, Rb, e, Or.inl ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm,
          fun hj => ⟨fun eb => VR_VRR_copy a ke ρ η _ ws ha.1 htb.1 hr hu ((hA hj).1 eb), fun eb => ?_⟩,
          fun hj => ⟨fun eb => VR_VRR_copy b ke ρ η _ ws ha.2 htb.2 hr hu ((hA' hj).1 eb), fun eb => ?_⟩⟩⟩
        · obtain ⟨q, c1, c2, c3, c4, c5⟩ := (hA hj).2 eb
          exact ⟨q, c1, c2, c3, c4, VR_VRR_copy a ke ρ η.unsee _ q ha.1 htb.1 hu hu c5⟩
        · obtain ⟨q, c1, c2, c3, c4, c5⟩ := (hA' hj).2 eb
          exact ⟨q, c1, c2, c3, c4, VR_VRR_copy b ke ρ η.unsee _ q ha.2 htb.2 hu hu c5⟩
      · refine ⟨n, Ra, Rb, e, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj; exact ⟨q, hq, VR_VRR_copy a ke ρ η _ q ha.1 htb.1 hr hu hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, VR_VRR_copy b ke ρ η _ q ha.2 htb.2 hr hu hv⟩
  | .tex κ b, ke, ρ, η, rt, ws, ha, htb, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [tb] at htb; simp only [VR] at hv; simp only [VRR]
      obtain ⟨n, rb, s, e, hc, hk, hv⟩ := hv
      refine ⟨n, rb, s, e, hc, hk, VR_VRR_copy b (some κ :: ke) ρ (η.push0 s) rb ws ha
        (by simpa using htb) (fun k hk1 hk S vs h => ?_) (fun k hk1 hk S vs h => ?_) hv⟩
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hr k (by simpa using hk1) (by simpa [KEnv.ask] using hk) S vs h
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hu k (by simpa using hk1) (by simpa [KEnv.ask] using hk) S vs h
  | .mu b, ke, ρ, η, rt, ws, ha, htb, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [tb] at htb; simp only [VR] at hv; simp only [VRR]
      refine VR_VRR_copy b (none :: ke) ρ _ rt ws ha (by simpa using htb)
        (fun k hk1 hk S vs h => ?_) (fun k hk1 hk S vs h => ?_) hv
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hr k (by simpa using hk1) (by simpa [KEnv.ask] using hk) S vs h
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hu k (by simpa using hk1) (by simpa [KEnv.ask] using hk) S vs h
  | .array _ _, _, _, _, _, _, _, _, _, _, _ => by simp only [VRR]
  | .unit, _, _, _, _, _, _, _, _, _, _ => by simp only [VRR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _ => by simp only [VRR]
  | .void, _, _, _, _, _, _, _, _, _, hv => by simp [VR] at hv
  | .intS _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .int, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .fix _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .code _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .ptr μ _, _, _, _, _, _, ha, _, _, _, hv => by
      simp only [VR] at hv; simp only [VRR]; refine ⟨hv, ?_⟩; cases μ <;> simp_all [Ty.affineIn]
  | .ptrOpt μ _, _, _, _, _, _, ha, _, _, _, hv => by
      simp only [VR] at hv; simp only [VRR]; refine ⟨hv, ?_⟩; cases μ <;> simp_all [Ty.affineIn]
  | .loc μ _, _, _, _, _, _, ha, _, _, _, hv => by
      simp only [VR] at hv; simp only [VRR]; refine ⟨hv, ?_⟩; cases μ <;> simp_all [Ty.affineIn]
  | .tok _ _, _, _, _, _, _, ha, _, _, _, _ => by simp [Ty.affineIn] at ha
  | .tok2 _ _ _ _, _, _, _, _, _, ha, _, _, _, _ => by simp [Ty.affineIn] at ha
  | .tokE _ _ _, _, _, _, _, _, ha, _, _, _, _ => by simp [Ty.affineIn] at ha
  | .share _, _, _, _, _, _, ha, _, _, _, _ => by simp [Ty.affineIn] at ha
  | .word _ _, _, _, _, _, _, ha, _, _, _, _ => by simp [Ty.affineIn] at ha
  | .word2 _ _, _, _, _, _, _, ha, _, _, _, _ => by simp [Ty.affineIn] at ha
  | .epair _ _, _, _, _, _, _, ha, _, _, _, _ => by simp [Ty.affineIn] at ha

/-- (P3) A closed non-affine type's values are values carrying nothing. -/
theorem VR_VRR_copy_closed {s : Ty} (hs : tb 0 s = true) (ha : Ty.affine s = false) {ρ : Nat → Nat}
    {η : TEnv} {rt : Shp} {ws : List Word} (hv : VR ρ η s rt ws) : VRR ρ η s rt ws .zero :=
  VR_VRR_copy s [] ρ η rt ws ha hs (fun _ hk => absurd hk (Nat.not_lt_zero _))
    (fun _ hk => absurd hk (Nat.not_lt_zero _)) hv

/-- (P3) Under `Coh`, `CohR` and `WitC`, copy-kinded variables' plain values
are resource-free values: the hypotheses of `VR_VRR_copy`. -/
theorem WitC_VRR {ke : KEnv} {η : TEnv} (hc : Coh η) (hr : CohR η) (hw : WitC ke η) :
    (∀ k, ke.ask k true (·.copy) = true → ∀ S vs, η.rels k S vs → η.rrs k S vs .zero) ∧
    (∀ k, ke.ask k true (·.copy) = true → ∀ S vs, η.urels k S vs → η.urrs k S vs .zero) :=
  ⟨fun k hk S vs h => ((hr k).1 (fun _ => 0) S vs .zero).2
      (VR_VRR_copy_closed (hc k).1.1 (hw k hk) (((hc k).2.1 (fun _ => 0) S vs).1 h)),
   fun k hk S vs h => ((hr k).2 (fun _ => 0) S vs .zero).2
      (VR_VRR_copy_closed (hc k).1.1 (hw k hk) (((hc k).2.2 (fun _ => 0) S vs).1 h))⟩

/-- (P3) A frame's non-affine values are values carrying nothing. -/
theorem VR_VRR_copy_frame {ke : KEnv} {η : TEnv} (hc : Coh η) (hr : CohR η) (hw : WitC ke η) {t : Ty}
    {ρ : Nat → Nat} {rt : Shp} {ws : List Word} (ha : Ty.affineIn ke t = false) (htb : tb ke.length t = true)
    (hv : VR ρ η t rt ws) : VRR ρ η t rt ws .zero :=
  VR_VRR_copy t ke ρ η rt ws ha htb (fun k _ => (WitC_VRR hc hr hw).1 k)
    (fun k _ => (WitC_VRR hc hr hw).2 k) hv

/-- (P3) The frame form at a frame invariant: `FInv` gives `WitC`, `EnvOK` gives
`Coh` and `CohR`. -/
theorem VR_VRR_copy_finv {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {p : Prog} (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) {t : Ty} {ρ' : Nat → Nat} {rt : Shp}
    {ws : List Word} (ha : Ty.affineIn cx.ke t = false) (htb : tb cx.ke.length t = true)
    (hv : VR ρ' η t rt ws) : VRR ρ' η t rt ws .zero :=
  VR_VRR_copy_frame hE.2.1 hE.2.2 hi.2.2.2.2.2.2.2.2.1 ha htb hv

end TermSound

namespace TermMem
open CoreLang CoreTerm TermRun TermClose TermSound
open WeakMem (Ts)

/-- (D3, P3) A value held in the thread's view, with its resources. -/
def EnvValR (η : TEnv) (T : Ty) (ws : List Word) (R : Res) : Prop :=
  VRR (fun _ => 0) (CE η) T (shp T) ws R ∧ Valid T ws

/-- (D3, P3) A value stored is a memory value, with the same resources. -/
theorem EnvValR.store {η : TEnv} {T : Ty} {ws : List Word} {R : Res} {V : Ts} (h : EnvValR η T ws R)
    (hS : SeenLE η V) :
    VRR (fun _ => 0) (CE η.unsee) T (shp T) (ws.map (bumpW V)) R ∧ Valid T (ws.map (bumpW V)) :=
  ⟨VRR_unsee V T (CE η) (CE η.unsee) _ _ _ R (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl rfl rfl
      (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl))
      (fun _ _ h => h) (LocAbove_bump V ws) (VRR_up _ _ _ _ _ (WLe_bump V ws) h.1),
    Valid_vals _ _ _ (WLe_bump V ws).vals h.2⟩

/-- (D3, P3) Forgetting the resources of a held value. -/
theorem EnvValR.envVal {η : TEnv} {T : Ty} {ws : List Word} {R : Res} (h : EnvValR η T ws R) :
    EnvVal η T ws :=
  ⟨VRR_VR T (RLink_of (Coh_CE _) (CohR_CE _)) h.1, h.2⟩

end TermMem

#print axioms TermMem.readable_latest
#print axioms TermMem.stepLoad_latest
#print axioms TermMem.stepLoadPair_latest
#print axioms TermMem.loadUnits_latest
#print axioms TermMem.MemOK_push
#print axioms TermMem.stepStore_promSub
#print axioms TermMem.storeUnits_growsF
#print axioms TermMem.storeUnits_wrF
#print axioms TermMem.storeUnits_latestF
#print axioms TermMem.storeUnits_newOKF
#print axioms TermMem.stepStore_cases
#print axioms TermMem.storeUnits_memOK
#print axioms TermMem.MemOK_pushPair
#print axioms TermMem.MemOK_mono
#print axioms TermMem.storeUnits_latest
#print axioms TermMem.OwnOK_load
#print axioms TermMem.OwnOK_store

#print axioms TermMem.alloc_ok
#print axioms TermMem.wc_of_accs
#print axioms TermMem.NoProm_grows
#print axioms TermMem.storeUnits_grows
#print axioms TermMem.loadUnits_frame
#print axioms TermMem.alloc_grows
#print axioms TermMem.storeUnits_nonempty
#print axioms TermMem.readable_of_latest
#print axioms TermMem.noStraddle_latest
#print axioms TermMem.loadUnits_nonempty
#print axioms TermMem.OwnOK_load_nonempty
#print axioms TermMem.OwnOK_plain
#print axioms TermMem.CellOK_map
#print axioms TermMem.storeUnits_newOK
#print axioms TermMem.storeUnits_wr
#print axioms TermMem.loadUnits_vWr
#print axioms TermMem.storeUnits_hid
#print axioms TermMem.alloc_hid
#print axioms TermMem.ShapeC_of_wc
#print axioms TermMem.alloc_latest
#print axioms TermMem.storeUnits_memOK0
#print axioms TermMem.alloc_ok0
#print axioms TermSound.VRR_unsee
#print axioms TermSound.VR_VRR_copy
#print axioms TermSound.VR_VRR_copy_closed
#print axioms TermSound.WitC_VRR
#print axioms TermSound.VR_VRR_copy_frame
#print axioms TermSound.VR_VRR_copy_finv
#print axioms TermMem.EnvValR.store
#print axioms TermMem.EnvValR.envVal
