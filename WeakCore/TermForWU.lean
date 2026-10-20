import WeakCore.TermB5
import WeakCore.TermStepPred
import WeakCore.TermPiece
import WeakCore.TermBlkZ
import WeakCore.KindSound

/-!
# TermForWU: a step's write at another thread's cell is a word unit or an RMW atom

Every message a typed, in-scope thread step appends (`tstep_newFW`), and every
own promise it fulfils (`tstep_lostFW`), at a cell the stepper does not own, is

* at a word unit (`WordUnit`: a non-ghost protocol word, or a word of a
  protocol pair), or
* at an RMW atom (`RmwAtom`: inside an `Int` cell component (`fetchCell`), a
  one-word component (`casCell`), or an epoch pair (`caspE`)), or
* the write of a `pub` store at a non-word reference (`PubShape`).

Buffer writes (`xchgAt`, `xchgAtF`, `bufInit`, `stl`, `stlw`), `own` stores and
`xchg` are at own cells; `rgn` stores and `xchg`s are out of scope.  The
system form is `tctx_forWU`.
-/

namespace TermForWU

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermB5
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- An address inside an RMW-written component `S` (laid out from word `o` of its
cell): an `Int`, a closed non-affine one-word leaf (`Solid`), or an epoch pair. -/
def RmwAtom (E : TEnv) (a : Address) : Prop :=
  ∃ c o S us, E.sto a.label = some c ∧ AtOff c.ty o S ∧ accs S = some us ∧ o ≤ a.offset ∧
    a.offset < o + nWords us ∧ (S = .int ∨ (accs S = some [.one] ∧ Solid S ∧ tb 0 S = true ∧ Ty.affine S = false) ∨
      ∃ n P, S = .epair (.lit n) P)

/-! ## 1. Targets -/

theorem cell_tgt {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ accs U = some us := by
  obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hi.2.1 hp (cell_cases hc) hea hb
  have hacc : accs U = some us := by
    rw [Fd_accs hFd, ← pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr,
      hus]
  exact ⟨c, U, hsto, hat, hFd, hacc⟩

#print axioms cell_tgt

theorem word_tgt {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {r : Idx} {P : Proto} {rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c n, η.sto b.label = some c ∧ AtOff c.ty b.offset (.word (.lit n) P) := by
  obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hvars hp ht hea hb
  simp only [cl, clI_zero] at hFd
  rw [Fd_word_eq hFd] at hat
  exact ⟨c, _, hsto, hat⟩

#print axioms word_tgt

theorem word2_tgt {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {r : Idx} {P : Proto2} {rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ (.word2 r P) ∨ t = .loc μ (.word2 r P))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c n, η.sto b.label = some c ∧ AtOff c.ty b.offset (.word2 (.lit n) P) := by
  obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hvars hp ht hea hb
  simp only [cl, clI_zero] at hFd
  rw [Fd_word2_eq hFd] at hat
  exact ⟨c, _, hsto, hat⟩

#print axioms word2_tgt

theorem epair_tgt {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {r : Idx} {P : ECounter} {rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ (.epair r P) ∨ t = .loc μ (.epair r P))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c n, η.sto b.label = some c ∧ AtOff c.ty b.offset (.epair (.lit n) P) := by
  obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hvars hp ht hea hb
  simp only [cl, clI_zero] at hFd
  rw [Fd_epair_eq hFd] at hat
  exact ⟨c, _, hsto, hat⟩

#print axioms epair_tgt

theorem int_tgt {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ .int ∨ t = .loc μ .int)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c, η.sto b.label = some c ∧ AtOff c.ty b.offset .int := by
  obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hvars hp ht hea hb
  rw [show cl ρ η.wit 0 0 Ty.int = Ty.int from rfl] at hFd
  rw [Fd_nonmu hFd (fun _ h => by cases h)] at hat
  exact ⟨c, hsto, hat⟩

#print axioms int_tgt

/-- Both words of a protocol pair are word units. -/
theorem w2_wu {E : TEnv} {b : Address} {c : Cell} {r : Idx} {P : Proto2} (hsto : E.sto b.label = some c)
    (hat : AtOff c.ty b.offset (.word2 r P)) : ∀ j, j < 2 → WordUnit E (offs b j)
  | 0, _ => ⟨c, hsto, .inr (.inl ⟨r, P, by show AtOff c.ty (b.offset + 0) _; rw [Nat.add_zero]; exact hat⟩)⟩
  | 1, _ => ⟨c, hsto, .inr (.inr ⟨r, P, Nat.le_add_left 1 b.offset,
      by show AtOff c.ty (b.offset + 1 - 1) _; rw [Nat.add_sub_cancel]; exact hat⟩)⟩
  | _ + 2, h => absurd h (by omega)

#print axioms w2_wu

/-- Every word of an RMW-written component is an RMW atom. -/
theorem rmw_at {E : TEnv} {b : Address} {c : Cell} {S : Ty} {us : List Acc} (hsto : E.sto b.label = some c)
    (hat : AtOff c.ty b.offset S) (hus : accs S = some us)
    (hk : S = .int ∨ (accs S = some [.one] ∧ Solid S ∧ tb 0 S = true ∧ Ty.affine S = false) ∨
      ∃ n P, S = .epair (.lit n) P) :
    ∀ j, j < nWords us → RmwAtom E (offs b j) :=
  fun _ hj => ⟨c, b.offset, S, us, hsto, hat, hus, Nat.le_add_right _ _,
    Nat.add_lt_add_left hj _, hk⟩

#print axioms rmw_at

theorem nWords_one : nWords [Acc.one] = 1 := by simp [nWords, Acc.size]
theorem nWords_two : nWords [Acc.two] = 2 := by simp [nWords, Acc.size]


/-! ## 1b. One-word leaves -/

/-- Substituting a closed non-affine type for a recursion variable keeps a type non-affine. -/
theorem affine_substT : ∀ (t : Ty) (s : Ty) (ke0 ke : KEnv), tb 0 s = true → Ty.affineIn [] s = false →
    Ty.affineIn (ke0 ++ none :: ke) t = false → Ty.affineIn (ke0 ++ ke) (Ty.substT ke0.length s t) = false := by
  intro t
  induction t with
  | tvar k =>
      intro s ke0 ke hs ha h
      simp only [Ty.substT]
      by_cases hk : k = ke0.length
      · subst hk
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [AffineCl.affineIn_closed hs _ []]; exact ha
      · have hb : (k == ke0.length) = false := beq_false_of_ne hk
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        by_cases hg : k > ke0.length
        · simp only [hg, ↓reduceIte]
          simp only [Ty.affineIn, KEnv.ask] at h ⊢
          obtain ⟨m, rfl⟩ : ∃ m, k = ke0.length + 1 + m := ⟨k - ke0.length - 1, by omega⟩
          rw [List.getElem?_append_right (by omega)] at h
          rw [List.getElem?_append_right (by omega)]
          rw [show ke0.length + 1 + m - ke0.length = m + 1 by omega] at h
          rw [show ke0.length + 1 + m - 1 - ke0.length = m by omega]
          simpa only [List.getElem?_cons_succ] using h
        · simp only [hg, ↓reduceIte]
          simp only [Ty.affineIn, KEnv.ask] at h ⊢
          rw [List.getElem?_append_left (by omega)] at h
          rw [List.getElem?_append_left (by omega)]
          exact h
  | prod a b iha ihb =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at h
      simp only [Ty.substT, Ty.affineIn, iha s ke0 ke hs ha h.1, ihb s ke0 ke hs ha h.2, Bool.or_self]
  | sum a b iha ihb =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at h
      simp only [Ty.substT, Ty.affineIn, iha s ke0 ke hs ha h.1, ihb s ke0 ke hs ha h.2, Bool.or_self]
  | array i t ih =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn] at h
      simp only [Ty.substT, Ty.affineIn, ih s ke0 ke hs ha h]
  | refine t ψ ih =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn] at h
      simp only [Ty.substT, Ty.affineIn, ih s ke0 ke hs ha h]
  | iall t ih =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn] at h
      simp only [Ty.substT, Ty.affineIn]
      exact ih (s.shiftI 0) ke0 ke (by rw [tb_shiftI]; exact hs) (by rw [KindSound.affine_shiftI]; exact ha) h
  | iex t ih =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn] at h
      simp only [Ty.substT, Ty.affineIn]
      exact ih (s.shiftI 0) ke0 ke (by rw [tb_shiftI]; exact hs) (by rw [KindSound.affine_shiftI]; exact ha) h
  | mu t ih =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn] at h
      simp only [Ty.substT, Ty.affineIn, tb_shiftT s hs (Nat.zero_le 0)]
      have e := ih s (none :: ke0) ke hs ha h
      simpa only [List.cons_append, List.length_cons] using e
  | tex κ t ih =>
      intro s ke0 ke hs ha h
      simp only [Ty.affineIn] at h
      simp only [Ty.substT, Ty.affineIn, tb_shiftT s hs (Nat.zero_le 0)]
      have e := ih s (some κ :: ke0) ke hs ha h
      simpa only [List.cons_append, List.length_cons] using e
  | ptr m t ih => intro s ke0 ke hs ha h; cases m <;> simp_all [Ty.substT, Ty.affineIn]
  | ptrOpt m t ih => intro s ke0 ke hs ha h; cases m <;> simp_all [Ty.substT, Ty.affineIn]
  | loc m t ih => intro s ke0 ke hs ha h; cases m <;> simp_all [Ty.substT, Ty.affineIn]
  | _ => intro s ke0 ke hs ha h; simp_all [Ty.substT, Ty.affineIn]

#print axioms affine_substT

/-- **The one-word leaf of a closed guarded non-affine one-word type**: at offset 0, a
`Solid`, closed, non-affine component with one word. -/
theorem one_leafM : ∀ (n : Nat) (T : Ty), TermBlkZ.skN T < n → Clo T → TermTv.mg T = true →
    accs T = some [Acc.one] → Ty.affine T = false →
    ∃ S, AtOff T 0 S ∧ Solid S ∧ accs S = some [Acc.one] ∧ tb 0 S = true ∧ Ty.affine S = false
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, T, hn, hc, hm, hL, ha => by
    cases T with
    | prod a b =>
      simp only [TermBlkZ.skN] at hn
      simp only [TermTv.mg, Bool.and_eq_true] at hm
      simp only [Ty.affine, Ty.affineIn, Bool.or_eq_false_iff] at ha
      obtain ⟨hca, hcb⟩ := TermBlkZ.Clo_prod hc
      obtain ⟨ua, ub, hua, hub⟩ := TermPiece.accs_prod_some (by rw [hL]; exact Option.some_ne_none _)
      have hLe : ua ++ ub = [Acc.one] := by
        simp only [accs, hua, hub] at hL
        exact Option.some.inj hL
      cases ua with
      | nil =>
        simp only [List.nil_append] at hLe
        subst hLe
        obtain ⟨S, hS, h1, h2, h3, h4⟩ := one_leafM n b (by omega) hcb hm.2 hub ha.2
        have hS2 : AtOff (.prod a b) (nWords [] + 0) S := AtOff.snd hua hS
        exact ⟨S, by simpa [nWords] using hS2, h1, h2, h3, h4⟩
      | cons x r =>
        simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at hLe
        obtain ⟨rfl, rfl, rfl⟩ := hLe
        obtain ⟨S, hS, h1, h2, h3, h4⟩ := one_leafM n a (by omega) hca hm.1 hua ha.1
        exact ⟨S, .fst hS, h1, h2, h3, h4⟩
    | mu s =>
      have hm0 := hm
      simp only [TermTv.mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hcU, haU, hat⟩ := TermBlkZ.mu_unfold_facts hc hm.1
      have hsk : TermBlkZ.skN (unfold1 (.mu s)) < n := by
        show TermBlkZ.skN (Ty.substT 0 (.mu s) s) < n
        rw [TermBlkZ.skN_substT s 0 _ hm.1]; simp only [TermBlkZ.skN] at hn; omega
      have haU2 : Ty.affine (unfold1 (.mu s)) = false := by
        show Ty.affineIn [] (Ty.substT 0 (.mu s) s) = false
        have hs0 : Ty.affineIn ([] ++ none :: []) s = false := by
          simpa [Ty.affine, Ty.affineIn] using ha
        simpa using affine_substT s (.mu s) [] [] hc.1 ha hs0
      obtain ⟨S, hS, h1, h2, h3, h4⟩ :=
        one_leafM n _ hsk hcU (TermTv.mg_unfold1 hm0) (by rw [haU]; exact hL) haU2
      exact ⟨S, hat _ _ hS, h1, h2, h3, h4⟩
    | array i e => simp [accs] at hL
    | _ =>
      exact ⟨_, .here (Or.inl (by rw [hL]; exact Option.some_ne_none _)),
        ⟨fun _ _ h => Ty.noConfusion h, fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩,
        hL, hc.1, ha⟩

#print axioms one_leafM

/-! ## 2. Per operation -/

/-- A `storeUnits` write at a cell the stepper does not own: a word unit or a
`pub` store at a non-word reference. -/
theorem units_cls {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {th : TTh} {x : String} {op : Op} {e : Expr}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hterm : th.term = .let_ x op e) (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s op pw b rel us ws) {j : Nat} (hj : j < nWords us)
    {cel : Cell} (hc : η.sto b.label = some cel) (hown : cel.owner ≠ some η.tid) :
    WordUnit (CE η) (offs b j) ∨ TermPiece.PubShape cx th := by
  cases op
  case store rl a v tok =>
    obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
    cases hop with
    | storeOwn hp _ hcl =>
        obtain ⟨c1, hs1, hmo⟩ := TermStepPred.cell_mode hi.2.1 hp hcl hea hb
        rw [hc] at hs1; cases hs1
        exact absurd (show cel.owner = some η.tid from hmo) hown
    | storePub hp hw hcl =>
        right
        rcases cell_cases hcl with rfl | rfl
        · exact ⟨x, rl, a, v, tok, e, _, hterm, .inl ⟨hp, hw⟩⟩
        · exact ⟨x, rl, a, v, tok, e, _, hterm, .inr ⟨hp, hw⟩⟩
    | storeRgn hp _ hcl => exact absurd hcl (hsc _ hp _ _)
    | storeCap hp _ hcl => exact absurd hcl (hsc _ hp _ _)
    | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
        obtain ⟨μ, ht⟩ := wordOf_cases hw
        simp only at ht
        have key : ∀ (t0 : Ty) (μ0 : Mode) (r0 : Idx) (P0 : Proto), cellOf t0 = some (μ0, Ty.word r0 P0) →
            cx.peek a = .ok t0 → WordUnit (CE η) (offs b j) ∨ TermPiece.PubShape cx th := by
          intro t0 μ0 r0 P0 hcl hp0
          obtain ⟨c, U, hsto, hat, hFd, hacc⟩ := cell_tgt hi hE htv hp0 hcl
            (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
          simp only [cl, clI_zero] at hFd
          rw [Fd_word_eq hFd] at hat hacc
          cases hg : P0.ghost
          · simp [accs, hg] at hacc
            subst hacc
            have hj0 : j = 0 := by rw [nWords_one] at hj; omega
            subst hj0
            rw [TermStep.offs_zero]
            exact .inl ⟨c, hsto, .inl ⟨_, P0, hg, hat⟩⟩
          · simp [accs, hg] at hacc
            subst hacc
            simp [nWords] at hj
        rcases ht with rfl | rfl
        · exact key _ μ _ _ rfl hp
        · exact key _ μ _ _ rfl hp
  case xchg a v =>
    obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
    cases hop with
    | xchg hp hx =>
        cases hx with
        | rgn _ hcl => exact absurd hcl (hsc _ hp _ _)
        | own _ hcl =>
            obtain ⟨c1, hs1, hmo⟩ := TermStepPred.cell_mode hi.2.1 hp hcl hea hb
            rw [hc] at hs1; cases hs1
            exact absurd (show cel.owner = some η.tid from hmo) hown
  case xchgAt =>
    obtain ⟨c1, hs1, hmo⟩ := TermStepPred.xchgAt_own hop hi htv hu
    rw [hc] at hs1; cases hs1
    exact absurd hmo hown
  case xchgAtF =>
    obtain ⟨c1, hs1, hmo⟩ := TermStepPred.xchgAtF_own hop hi htv hu
    rw [hc] at hs1; cases hs1
    exact absurd hmo hown
  case bufInit =>
    obtain ⟨c1, hs1, hmo⟩ := TermStepPred.bufInit_own hop hi htv hu
    rw [hc] at hs1; cases hs1
    exact absurd hmo hown
  case stl =>
    obtain ⟨c1, hs1, hmo⟩ := TermStepPred.stl_own hop hi htv hu
    rw [hc] at hs1; cases hs1
    exact absurd hmo hown
  case stlw =>
    obtain ⟨c1, hs1, hmo⟩ := TermStepPred.stlw_own hop hi htv hu
    rw [hc] at hs1; cases hs1
    exact absurd hmo hown
  all_goals simp [TermFul.UnitsOp] at hu

#print axioms units_cls

/-- A `fetch`'s RMW target: a non-ghost protocol word or an `Int` component. -/
theorem fetch_cls {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {b : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some b) :
    WordUnit (CE η) b ∨ RmwAtom (CE η) b := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc0 | ⟨r, hc0, -⟩
      all_goals
        obtain ⟨c, hsto, hat⟩ := int_tgt hi.2.1 hp (cell_cases hc0) hea hb
        have h := rmw_at (E := CE η) hsto hat rfl (.inl rfl) 0 (by rw [nWords_one]; omega)
        rw [TermStep.offs_zero] at h
        exact .inr h
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      have hg := pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hok.1.1.1.1, hat⟩⟩

#print axioms fetch_cls

/-- A `cas`'s RMW target: a non-ghost protocol word or a one-word component. -/
theorem cas_cls {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {b : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some b) :
    WordUnit (CE η) b ∨ RmwAtom (CE η) b := by
  cases hT with
  | casCell hp _ hc hraw haff =>
      have hraw0 := hraw
      rcases hc with hc0 | ⟨r, hc0, -⟩
      all_goals
        obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hi.2.1 hp (cell_cases hc0) hea hb
        have hV : accs (cl ρ η.wit 0 0 _) = some [.one] := accs_cl_one hraw0
        have hacc : accs U = some [.one] := (Fd_accs hFd).trans hV
        have htb := tb_cellOf (peek_tb htv hp) hc0
        have hVa := AffineCl.affine_cl0 ρ η.wit cx.ke (fun k => (hE.2.1 k).1)
          (fun k _ hk => hi.2.2.2.2.2.2.2.2.1 k hk) _ haff htb
        have hVm := mg_cl (ρ := ρ) (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) _ 0 0
          (mg_cellOf (peek_mg htv hp) hc0)
        obtain ⟨S, hS, hsol, hSa, hStb, hSaf⟩ := one_leafM _ _ (Nat.lt_succ_self _)
          (Clo_cl (fun k => (hE.2.1 k).1) ρ _) hVm hV hVa
        have hat2 : AtOff c.ty b.offset S := by
          have := AtOff_trans (AtOff_trans hat (Fd_AtOff hFd (by rw [hacc]; exact Option.some_ne_none _))) hS
          simpa using this
        have h := rmw_at (E := CE η) hsto hat2 hSa (.inr (.inl ⟨hSa, hsol, hStb, hSaf⟩)) 0
          (by rw [nWords_one]; omega)
        rw [TermStep.offs_zero] at h
        exact .inr h
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        have hg := pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep
        obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
        exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
      · rw [hw] at hnw; cases hnw

#print axioms cas_cls

/-- A `casp`'s two words: both word units (a protocol pair) or both RMW atoms
(an epoch pair). -/
theorem casp_cls {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {acq rel : Bool} {w e0 e1 v0 v1 : At} {tn : String} {ok fail : Expr}
    {tw : Ty} {pw : Word} {A : Address}
    (hT : Typed p cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hsc : StepScope cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hi : FInv ρ η σs K cx env) (hea : evalAt env w = some (tw, [pw])) (hb : addrOf pw = some A) :
    (∀ j, j < 2 → WordUnit (CE η) (offs A j)) ∨ (∀ j, j < 2 → RmwAtom (CE η) (offs A j)) := by
  have hp : ∃ t, cx.peek w = .ok t := by cases hT <;> exact ⟨_, ‹_›⟩
  obtain ⟨t, hp⟩ := hp
  obtain ⟨μ, u, ht, -, hu⟩ := hsc t hp
  rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
  · obtain ⟨c, n, hsto, hat⟩ := word2_tgt hi.2.1 hp ht hea hb
    exact .inl (w2_wu (E := CE η) hsto hat)
  · obtain ⟨c, n, hsto, hat⟩ := epair_tgt hi.2.1 hp ht hea hb
    right
    intro j hj
    exact rmw_at (E := CE η) hsto hat rfl (.inr (.inr ⟨n, P, rfl⟩)) j (by rw [nWords_two]; exact hj)

#print axioms casp_cls

/-! ## 3. A thread step -/

/-- **New messages at foreign cells**: every message a typed, in-scope thread
step appends at a cell the stepper does not own is at a word unit or an RMW
atom, or the step is a `pub` store at a non-word reference. -/
theorem tstep_newFW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg) (cel : Cell), mem.size ≤ t → r.1[t]? = some m → η.sto m.loc.label = some cel →
      cel.owner ≠ some η.tid → WordUnit (CE η) m.loc ∨ RmwAtom (CE η) m.loc ∨ TermPiece.PubShape cx th := by
  intro t m cel ht hmt hc hown
  rcases tstep_newR (MemInv_promLt hm) h t m ht hmt with hF | hN
  · have h0 : η.sto m.loc.label = none := (fresh_blank hm hF).1
    rw [h0] at hc; cases hc
  rcases hN with ⟨x, op, e, hterm, b, us, j, hn, hl, hr⟩ | ⟨acq, rel, w, e, v, tn, ok, fail, tw, pw, hterm, hea, hb⟩ |
      ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, tw, pw, A, hterm, hea, hb, hl⟩
  · have hj := roleR_lt hr
    have hsc0 := hsc
    rw [hterm] at hT hsc0
    cases hT with
    | let_ hop _ =>
        rcases hn with ⟨pw, rel, ws, hu⟩ | ⟨rel, a, v0, v1, tk, t', pw, rfl, hea, hb, rfl⟩ |
            ⟨o, acq, rel, a, v, t', pw, rfl, hea, hb, rfl⟩
        · rw [hl] at hc ⊢
          exact (units_cls hterm hop hsc0 hi hE htv hu hj hc hown).elim .inl (fun h => .inr (.inr h))
        · have hp : ∃ t, cx.peek a = .ok t := by cases hop <;> exact ⟨_, ‹_›⟩
          obtain ⟨t0, hp⟩ := hp
          obtain ⟨μ, r0, P, ht0, -⟩ := hsc0 t0 hp
          obtain ⟨c, n, hsto, hat⟩ := word2_tgt hi.2.1 hp ht0 hea hb
          rw [hl]
          exact .inl (w2_wu (E := CE η) hsto hat j (by rw [nWords_two] at hj; exact hj))
        · have hj0 : j = 0 := by rw [nWords_one] at hj; omega
          subst hj0
          rw [hl, TermStep.offs_zero]
          exact (fetch_cls hop hsc0 hi hE htv hm hea hb).elim .inl (fun h => .inr (.inl h))
  · rw [hterm] at hT hsc
    exact (cas_cls hT hsc hi hE htv hm hea hb).elim .inl (fun h => .inr (.inl h))
  · rw [hterm] at hT hsc
    have hj : ∃ j, j < 2 ∧ m.loc = offs A j := by
      rcases hl with ⟨hl, -⟩ | ⟨hl, -⟩
      · exact ⟨0, by omega, by rw [hl, TermStep.offs_zero]⟩
      · exact ⟨1, by omega, hl⟩
    obtain ⟨j, hj, hl0⟩ := hj
    rw [hl0]
    rcases casp_cls hT hsc hi hea hb with hw | hw
    · exact .inl (hw j hj)
    · exact .inr (.inl (hw j hj))

#print axioms tstep_newFW

/-- **Lost promises at foreign cells**: every own promise a typed, in-scope
thread step fulfils at a cell the stepper does not own is at a word unit or an
RMW atom, or the step is a `pub` store at a non-word reference. -/
theorem tstep_lostFW {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg) (cel : Cell), t ∈ th.promises → t ∉ r.2.2.promises → mem[t]? = some m →
      η.sto m.loc.label = some cel → cel.owner ≠ some η.tid →
      WordUnit (CE η) m.loc ∨ RmwAtom (CE η) m.loc ∨ TermPiece.PubShape cx th := by
  intro t m cel ht hn hmt hc hown
  obtain ⟨m0, hm0, hsw, -, -⟩ := (TermFul.tstep_fulfil (MemInv_promLt hm) (MemInv_nopair hm) h).2 t ht hn
  obtain rfl : m0 = m := Option.some.inj (hm0.symm.trans hmt)
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · have hsc0 := hsc
    rw [hterm] at hT hsc0
    cases hT with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj1, -, hl, -⟩ |
            ⟨o, acq, rel, a, v, t0, t1, pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · rw [hl] at hc ⊢
          exact (units_cls hterm hop hsc0 hi hE htv hu (TermFul.OneAt_lt hj1) hc hown).elim .inl
            (fun h => .inr (.inr h))
        · exact (fetch_cls hop hsc0 hi hE htv hm hea hb).elim .inl (fun h => .inr (.inl h))
  · rw [hterm] at hT hsc
    exact (cas_cls hT hsc hi hE htv hm hea hb).elim .inl (fun h => .inr (.inl h))

#print axioms tstep_lostFW

/-! ## 4. At a reachable thread step -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **Foreign writes are word units or RMW atoms (at the system)**: at a thread
step (`TCtx`) typed at a cut (`EnvAt`, with its `MemInv`), every new message and
every lost own promise at a cell not the stepper's, unless the step is a `pub`
store at a non-word reference, is at a `WordUnit` or an `RmwAtom`. -/
theorem tctx_forWU {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)) :
    (∀ (t : Nat) (m : Msg) (cel : Cell), c.mem.size ≤ t → c'.mem[t]? = some m →
        (CE η).sto m.loc.label = some cel → cel.owner ≠ some i → ¬ TermPiece.PubShape cx th →
        WordUnit (CE η) m.loc ∨ RmwAtom (CE η) m.loc) ∧
    (∀ (t : Nat) (m : Msg) (cel : Cell), t ∈ th.promises → t ∉ r.2.2.promises → c.mem[t]? = some m →
        (CE η).sto m.loc.label = some cel → cel.owner ≠ some i → ¬ TermPiece.PubShape cx th →
        WordUnit (CE η) m.loc ∨ RmwAtom (CE η) m.loc) := by
  have hs0 := hsc X Y
  obtain ⟨-, htid, hE, hT, htv, hF, -⟩ := Y
  have hFi : FInv ρ η th.σs (Resume p th.stack) cx th.env :=
    FInvR_FInv (htv.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hF
  have fin : ∀ {a : Address}, WordUnit (CE η) a ∨ RmwAtom (CE η) a ∨ TermPiece.PubShape cx th → ¬ TermPiece.PubShape cx th →
      WordUnit (CE η) a ∨ RmwAtom (CE η) a := fun h hp => h.imp_right (fun h => h.resolve_right hp)
  rcases hs0 with hs | hR
  · refine ⟨fun t m cel ht hm1 hc hown hp => ?_, fun t m cel ht hn hm1 hc hown hp => ?_⟩
    · have hmt : r.1[t]? = some m := by rw [← X.e1]; exact hm1
      exact fin (tstep_newFW hE hT.1 htv hFi hm hs X.hr t m cel ht hmt hc (by rw [htid]; exact hown)) hp
    · exact fin (tstep_lostFW hE hT.1 htv hFi hm hs X.hr t m cel ht hn hm1 hc (by rw [htid]; exact hown)) hp
  · have hk := frame_keep hR hT.1 hT.2 hF hE htv hm r X.hr
    refine ⟨fun t m cel ht hm1 _ _ _ => ?_, fun t m cel ht hn _ _ _ _ => ?_⟩
    · have hmt : r.1[t]? = some m := by rw [← X.e1]; exact hm1
      have hk1 : r.1 = c.mem := hk.1
      rw [hk1, Array.getElem?_eq_none ht] at hmt; cases hmt
    · have hk2 : r.2.2.promises = th.promises := hk.2.1
      exact absurd (hk2 ▸ ht) hn

#print axioms tctx_forWU

end

end TermForWU
