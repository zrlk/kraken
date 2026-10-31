import WeakCore.TermLiveC
/-! # Liveness item 15 C, critical-section form (G3)

The held branch of liveness item 15 C, extended from the single release store to a *critical section*: a
thread anywhere on a decidable straight-line path that ends in the token release store (scope 1), or ends in a
call `f (mv, tk)` to an `unlockD`-shaped library release (scope 2), is the holder.

LIMITS:
* Only straight-line `let` paths (no branch, no `call`/`ret`/`tail` before the endpoint).  The `cas → ret` window
  inside `lock` (between the successful `cas` and the caller binding the token), and `unlockD`'s own `split`/`fld 0`
  steps before its store, are NOT covered.
* Ticket locks: no ticket-lock instance is claimed (the release of a ticket lock is not a single token store;
  see `NoTicket` at TermMain:513).
* Reachability / non-vacuity is OPEN: no concrete mutex/seqlock `Setting` is constructed.
* No soundness-API change. -/

namespace TermLiveC
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermLiveMach TermLiveL3
open CoreTyping TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermSpawn
open WeakMem (Arch Address)

/-- (as in `S2Spike3`) `mutexP`'s value `1` is held. -/
theorem heldV_mutexP_one : TermLiveHeld.HeldV mutexP (.num 1) := ⟨1, ⟨0, 1, false⟩, 0, rfl, rfl, rfl⟩
/-- (as in `S2Spike3`) `seqP`'s odd values are held. -/
theorem heldV_seqP_odd (j : Nat) : TermLiveHeld.HeldV seqP (.num (2 * j + 1)) := ⟨1, ⟨2, 1, false⟩, j, rfl, rfl, rfl⟩

/-! ## The decidable path -/

/-- Whitelisted operations: their `OpT` rules neither add facts nor call, and change the context only by
`use`/`bind`, `fenceCx`, a `torn` entry, or (`loadWord` only) one `observeCx` push (an index shift). -/
def opSafe : Op → Bool
  | .atom _ | .pair _ _ | .inl _ _ | .inr _ _ | .add _ _ | .sub _ _ | .new _ _ | .null _ _ | .fold _ _
  | .fld _ _ | .load _ _ | .store _ _ _ _ | .fence _ | .validate _ | .bits _ _ _ | .bit1 _ _ | .zero _
  | .cvt _ _ _ | .toInt _ | .asLanes _ _ _ | .fop _ _ _ | .fcmp _ _ _ | .fop1 _ _ => true
  | .isTy _ _ => false
  | _ => false

/-- `op` does not mention `y`, except as the base of a field locative `fld i y` (which, on a shared cell, only
peeks; on an `own` cell it consumes `y`, and then the endpoint cannot type). -/
def noUseOf (y : String) : Op → Bool
  | .fld _ _ => true
  | op => !(TermScope.opAts op).contains (.var y)

/-- The release endpoint: `store _ a _ (some tk)`. -/
def tokEnd (a tk : String) : Op → Bool
  | .store _ (.var a') _ (some (.var t')) => a' == a && t' == tk
  | _ => false

/-- One safe step of a path guarding `a` and `tk`: binds neither, whitelisted, `tk` unmentioned, `a` not used. -/
def pathStep (a tk x : String) (op : Op) : Bool :=
  x != a && x != tk && opSafe op && noUseOf a op && !(TermScope.opAts op).contains (.var tk)

/-- **Scope (1).** A straight-line `let` path from the current term to the token store on `a` with `tk`. -/
def TokPath (a tk : String) : Expr → Bool
  | .let_ x op e => tokEnd a tk op || (pathStep a tk x op && TokPath a tk e)
  | _ => false

/-- The library-release endpoint: `let q = pair mv tk in let _ = call f is q ts in _`. -/
def callEnd (f mv tk x : String) (op : Op) (e : Expr) : Bool :=
  match op, e with
  | .pair (.var m') (.var t'), .let_ _ (.call f' _ (.var q) _) _ =>
      m' == mv && t' == tk && f' == f && q == x && x != mv && x != tk
  | _, _ => false

/-- **Scope (2).** A straight-line `let` path to `call f (pair mv tk)`, `mv` the shared cell holding the word. -/
def TokPathCall (f mv tk : String) : Expr → Bool
  | .let_ x op e => callEnd f mv tk x op e || (pathStep mv tk x op && TokPathCall f mv tk e)
  | _ => false

/-! ## Context bookkeeping for the safe steps -/

/-- A variable found with a live flag peeks at its type. -/
theorem peek_of_find {cx : Cx} {y y' : String} {t : Ty} (h : cx.vars.find? (·.1 == y) = some (y', t, true)) :
    cx.peek (.var y) = .ok t := by
  obtain ⟨c₁, hu, -⟩ := TermSpawnSim.use_var_true h
  exact (use_cases hu).1

/-- `peek` reads only the variables. -/
theorem peek_vars {c c' : Cx} (h : c'.vars = c.vars) (a : At) : c'.peek a = c.peek a := by
  cases a <;> simp [Cx.peek, Cx.find, h]

/-- Using an atom only clears flags: whatever peeks after it peeked before; facts and kinds are kept. -/
theorem use_back {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) :
    (∀ y u, c₁.peek (.var y) = .ok u → cx.peek (.var y) = .ok u) ∧ c₁.facts = cx.facts ∧ c₁.ke = cx.ke := by
  obtain ⟨-, hc⟩ := use_cases h
  rcases hc with ⟨-, rfl⟩ | ⟨z, -, rfl⟩
  · exact ⟨fun _ _ h => h, rfl, rfl⟩
  · refine ⟨fun y u hp => ?_, rfl, rfl⟩
    have hf := peek_var hp
    have hf2 : (cx.vars.map (markU z)).find? (·.1 == y) = some (y, u, true) := hf
    rw [find_map_flags _ _ (markU_fst z)] at hf2
    cases he : cx.vars.find? (·.1 == y) with
    | none => rw [he] at hf2; cases hf2
    | some e =>
      rw [he] at hf2
      have hm : markU z e = (y, u, true) := by simpa using hf2
      have hb : e = (y, u, true) := by
        unfold markU at hm
        split at hm
        · simp at hm
        · exact hm
      rw [hb] at he
      exact peek_of_find he

/-- Binding a fresh `x` keeps every other variable, the facts and the kinds. -/
theorem bind_back {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    (∀ y u, y ≠ x → c'.peek (.var y) = .ok u → cx.peek (.var y) = .ok u) ∧ c'.facts = cx.facts ∧
      c'.ke = cx.ke := by
  have he := bind_eq h
  subst he
  refine ⟨fun y u hy hp => ?_, rfl, rfl⟩
  have hf := peek_var hp
  have hf2 : ((x, t, true) :: cx.vars).find? (·.1 == y) = some (y, u, true) := hf
  rw [List.find?_cons_of_neg (by intro hc; simp at hc; subst hc; exact hy rfl)] at hf2
  exact peek_of_find hf2

/-- A variable peeked after an index `push` was there before, at the unshifted type. -/
theorem push_back {cx : Cx} {n y : String} {u : Ty} (hp : (cx.push n).peek (.var y) = .ok u) :
    ∃ t0, cx.peek (.var y) = .ok t0 ∧ u = t0.shiftI 0 := by
  have hf := peek_var hp
  have hf2 : (cx.vars.map fun (x, t, b) => (x, t.shiftI 0, b)).find? (·.1 == y) = some (y, u, true) := hf
  rw [find_map_flags _ _ (fun e => by obtain ⟨_, _, _⟩ := e; rfl)] at hf2
  cases he : cx.vars.find? (·.1 == y) with
  | none => rw [he] at hf2; cases hf2
  | some e =>
    rw [he] at hf2
    obtain ⟨y', t0, b⟩ := e
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf2
    obtain ⟨-, h2, h3⟩ := hf2
    subst h3
    exact ⟨t0, peek_of_find he, h2.symm⟩

/-- `fenceCx` keeps the variables, the facts and the kinds. -/
theorem fenceCx_keeps (cx : Cx) (f : Fence) :
    (fenceCx cx f).vars = cx.vars ∧ (fenceCx cx f).facts = cx.facts ∧ (fenceCx cx f).ke = cx.ke := by
  cases f <;> exact ⟨rfl, rfl, rfl⟩

theorem stab_b {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    ((∀ y u, y ≠ x → c'.peek (.var y) = .ok u → cx.peek (.var y) = .ok u) ∧ c'.facts = cx.facts) ∧
      c'.ke = cx.ke :=
  ⟨⟨(bind_back h).1, (bind_back h).2.1⟩, (bind_back h).2.2⟩

theorem stab_ub {cx c₁ c' : Cx} {x : String} {a : At} {t t' : Ty} (hu : cx.use a = .ok (t, c₁))
    (h : c₁.bind x t' = .ok c') :
    ((∀ y u, y ≠ x → c'.peek (.var y) = .ok u → cx.peek (.var y) = .ok u) ∧ c'.facts = cx.facts) ∧
      c'.ke = cx.ke := by
  obtain ⟨h1, f1, k1⟩ := use_back hu
  obtain ⟨h2, f2, k2⟩ := bind_back h
  exact ⟨⟨fun y u hy hp => h1 y u (h2 y u hy hp), f2.trans f1⟩, k2.trans k1⟩

theorem stab_uub {cx c₁ c₂ c' : Cx} {x : String} {a b : At} {t u0 t' : Ty} (hu : cx.use a = .ok (t, c₁))
    (hu2 : c₁.use b = .ok (u0, c₂)) (h : c₂.bind x t' = .ok c') :
    ((∀ y u, y ≠ x → c'.peek (.var y) = .ok u → cx.peek (.var y) = .ok u) ∧ c'.facts = cx.facts) ∧
      c'.ke = cx.ke := by
  obtain ⟨h1, f1, k1⟩ := use_back hu
  obtain ⟨⟨h2, f2⟩, k2⟩ := stab_ub hu2 h
  exact ⟨⟨fun y u hy hp => h1 y u (h2 y u hy hp), f2.trans f1⟩, k2.trans k1⟩

/-! ## Typing inversion (peek stability) -/

/-- Peek stability across one safe step: every variable other than the bound one that is visible after the
step was visible before, either at the same type with the same facts, or (`loadWord`: one `observeCx` push) at
the unshifted type with the facts shifted; the kinds are kept. -/
theorem opT_stable {p : Prog} {cx c' : Cx} {x : String} {op : Op}
    (hop : OpT p cx x op c') (hs : opSafe op = true) :
    (((∀ y u, y ≠ x → c'.peek (.var y) = .ok u → cx.peek (.var y) = .ok u) ∧ c'.facts = cx.facts) ∨
      ((∀ y u, y ≠ x → c'.peek (.var y) = .ok u → ∃ t0, cx.peek (.var y) = .ok t0 ∧ u = t0.shiftI 0) ∧
        c'.facts = cx.facts.map fun (q : Nat × Idx) => (q.1 + 1, q.2.shift 0))) ∧ c'.ke = cx.ke := by
  cases hop with
  | atom hu hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | pair hu hu2 hb => exact ⟨.inl (stab_uub hu hu2 hb).1, (stab_uub hu hu2 hb).2⟩
  | inl _ hu hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | inr _ hu hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | addS _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | addI _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | subS _ _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | new hu _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | null _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | fold _ hu _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | fldOwn _ _ _ _ hu hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | fldShared _ _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | loadWord _ _ _ hb =>
    obtain ⟨h2, f2, k2⟩ := bind_back hb
    refine ⟨.inr ⟨fun y u hy hp => ?_, f2⟩, k2⟩
    have hp2 := h2 y u hy hp
    exact push_back ((peek_vars (c' := observeCx cx x _ _) (c := cx.push x) rfl (.var y)).symm.trans hp2)
  | loadOwn _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | loadPub _ _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | loadRgn _ _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | loadCap _ _ _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | loadTorn _ _ _ _ _ _ =>
    exact ⟨.inl ⟨fun y u _ hp => by rw [← hp]; exact (peek_vars rfl _).symm, rfl⟩, rfl⟩
  | storeWordGive _ _ hu _ _ _ _ _ _ _ _ _ _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | storeWordKeep _ _ hu _ _ _ _ _ _ _ _ _ _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | storeWordHand _ _ hu _ _ _ _ _ _ _ _ _ _ _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | storeOwn _ _ _ _ hu _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | storePub _ _ _ _ hu _ _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | storeRgn _ _ _ _ hu _ _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | storeCap _ _ _ _ hu _ _ _ hb => exact ⟨.inl (stab_ub hu hb).1, (stab_ub hu hb).2⟩
  | fence hb =>
    obtain ⟨h2, f2, k2⟩ := bind_back hb
    obtain ⟨v0, f0, k0⟩ := fenceCx_keeps cx _
    exact ⟨.inl ⟨fun y u hy hp => by rw [← h2 y u hy hp]; exact (peek_vars v0 _).symm, f2.trans f0⟩,
      k2.trans k0⟩
  | validate _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | bits _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | bit1 _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | zero _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | cvt _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | toInt _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | asLanes _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | fop _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | fcmp _ _ _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | fop1 _ _ hb => exact ⟨.inl (stab_b hb).1, (stab_b hb).2⟩
  | _ => simp [opSafe] at hs

/-! ## Index shifts -/

theorem wordOf_shiftI (c : Nat) (t : Ty) :
    wordOf (t.shiftI c) = (wordOf t).map (fun q => (q.1.shift c, q.2)) := by
  cases t with
  | ptr μ s => cases s <;> rfl
  | loc μ s => cases s <;> rfl
  | _ => rfl

theorem cellOf_shiftI (c : Nat) (t : Ty) :
    cellOf (t.shiftI c) = (cellOf t).map (fun q => (q.1.shift c, q.2.shiftI c)) := by
  cases t <;> rfl

theorem wordFreeIn_shiftI (ke : KEnv) (c : Nat) (t : Ty) :
    Ty.wordFreeIn ke (t.shiftI c) = Ty.wordFreeIn ke t := by
  induction t generalizing c <;> first | rfl | simp only [Ty.shiftI, Ty.wordFreeIn, *]

theorem tok_some_shiftI {t : Ty} {c : Nat} {r i : Idx} {P : Proto} (h : t.shiftI c = .tok r (some (P, i))) :
    ∃ r0 i0, t = .tok r0 (some (P, i0)) ∧ r = r0.shift c := by
  cases t with
  | tok r0 o =>
    cases o with
    | none => simp [Ty.shiftI] at h
    | some q =>
      obtain ⟨P0, i0⟩ := q
      simp [Ty.shiftI] at h
      obtain ⟨h1, rfl, -⟩ := h
      exact ⟨r0, i0, rfl, h1.symm⟩
  | _ => simp [Ty.shiftI] at h

/-- An index equation entailed after a `push` between shifted indices is entailed before it. -/
theorem eqI_unshift {cx c' : Cx} {r r' : Idx}
    (hf : c'.facts = cx.facts.map fun (q : Nat × Idx) => (q.1 + 1, q.2.shift 0))
    (h : EqI c' (r.shift 0) (r'.shift 0)) : EqI cx r r' := by
  intro ρ hs
  have h1 : ev (vins 0 0 ρ) (r.shift 0) = ev (vins 0 0 ρ) (r'.shift 0) :=
    h (vcons 0 ρ) (by rw [hf]; exact Sat_push 0 hs)
  rw [ev_shift 0 0 ρ r, ev_shift 0 0 ρ r'] at h1
  exact h1

theorem eqI_same {cx c' : Cx} {r r' : Idx} (hf : c'.facts = cx.facts) (h : EqI c' r r') : EqI cx r r' :=
  fun ρ hs => h ρ (by rw [hf]; exact hs)

theorem tokEnd_inv {a tk : String} {op : Op} (h : tokEnd a tk op = true) :
    ∃ rel v, op = .store rel (.var a) v (some (.var tk)) := by
  unfold tokEnd at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, rfl⟩
  · simp at h

theorem pathStep_inv {a tk x : String} {op : Op} (h : pathStep a tk x op = true) :
    x ≠ a ∧ x ≠ tk ∧ opSafe op = true := by
  simp only [pathStep, Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩

/-- **Inversion, scope (1).** A typed term on a `TokPath` holds, at its own context, either (word case: the
endpoint typed by `storeWordGive/Keep/Hand`) `a` a word reference of `P` at `r` and `tk` a live token
`tok r' (P, i)` with `r = r'` entailed, or (plain case: `storeOwn/Pub/Rgn/Cap`, the token ignored) `a` a non-word
cell reference with a word-free pointee (refuted at runtime by `plain_store_not_word`). -/
theorem typed_tokpath_inv {p : Prog} {cx : Cx} {a tk : String} {e : Expr}
    (hT : Typed p cx e) (hp : TokPath a tk e = true) :
    (∃ (t : Ty) (r r' i : Idx) (P : Proto), cx.peek (.var a) = .ok t ∧ wordOf t = some (r, P) ∧
      cx.peek (.var tk) = .ok (.tok r' (some (P, i))) ∧ EqI cx r r') ∨
    (∃ (t u : Ty) (μ : Mode), cx.peek (.var a) = .ok t ∧ cellOf t = some (μ, u) ∧
      Ty.wordFreeIn cx.ke u = true) := by
  induction e generalizing cx with
  | let_ x op e ih =>
    cases hT with
    | let_ hop hT1 =>
      simp only [TokPath, Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with hend | ⟨hstep, hp⟩
      · obtain ⟨rel, v, rfl⟩ := tokEnd_inv hend
        cases hop with
        | storeWordGive hpk hwd hu hrr =>
          exact .inl ⟨_, _, _, _, _, hpk, hwd, (use_cases hu).1, eqI_same (use_back hu).2.1 hrr⟩
        | storeWordKeep hpk hwd hu hrr =>
          exact .inl ⟨_, _, _, _, _, hpk, hwd, (use_cases hu).1, eqI_same (use_back hu).2.1 hrr⟩
        | storeWordHand hpk hwd hu hrr =>
          exact .inl ⟨_, _, _, _, _, hpk, hwd, (use_cases hu).1, eqI_same (use_back hu).2.1 hrr⟩
        | storeOwn hpk _ hc hwf => exact .inr ⟨_, _, _, hpk, hc, hwf⟩
        | storePub hpk _ hc hwf => exact .inr ⟨_, _, _, hpk, hc, hwf⟩
        | storeRgn hpk _ hc hwf => exact .inr ⟨_, _, _, hpk, hc, hwf⟩
        | storeCap hpk _ hc hwf => exact .inr ⟨_, _, _, hpk, hc, hwf⟩
      · obtain ⟨hxa, hxt, hsafe⟩ := pathStep_inv hstep
        obtain ⟨hst, hke⟩ := opT_stable hop hsafe
        rcases ih hT1 hp with ⟨t, r, r', i, P, hpa, hwd, hpt, hrr⟩ | ⟨t, u, μ, hpa, hc, hwf⟩
        · rcases hst with ⟨hb, hf⟩ | ⟨hb, hf⟩
          · exact .inl ⟨t, r, r', i, P, hb a t (Ne.symm hxa) hpa, hwd, hb tk _ (Ne.symm hxt) hpt,
              eqI_same hf hrr⟩
          · obtain ⟨t0, hpa0, rfl⟩ := hb a t (Ne.symm hxa) hpa
            obtain ⟨t1, hpt0, ht1⟩ := hb tk _ (Ne.symm hxt) hpt
            obtain ⟨r1, i1, rfl, rfl⟩ := tok_some_shiftI ht1.symm
            rw [wordOf_shiftI] at hwd
            cases hw0 : wordOf t0 with
            | none => rw [hw0] at hwd; cases hwd
            | some q =>
              rw [hw0] at hwd
              obtain ⟨r0, P0⟩ := q
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwd
              obtain ⟨rfl, rfl⟩ := hwd
              exact .inl ⟨t0, r0, r1, i1, P0, hpa0, hw0, hpt0, eqI_unshift hf hrr⟩
        · rw [hke] at hwf
          rcases hst with ⟨hb, -⟩ | ⟨hb, -⟩
          · exact .inr ⟨t, u, μ, hb a t (Ne.symm hxa) hpa, hc, hwf⟩
          · obtain ⟨t0, hpa0, rfl⟩ := hb a t (Ne.symm hxa) hpa
            rw [cellOf_shiftI] at hc
            cases hc0 : cellOf t0 with
            | none => rw [hc0] at hc; cases hc
            | some q =>
              rw [hc0] at hc
              obtain ⟨μ0, u0⟩ := q
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
              obtain ⟨-, rfl⟩ := hc
              rw [wordFreeIn_shiftI] at hwf
              exact .inr ⟨t0, u0, μ0, hpa0, hc0, hwf⟩
  | _ => simp [TokPath] at hp

/-- A peeked token is a counted unit of its region (the `peek` form of `TermLiveHeld.tok_frame`). -/
theorem peek_tok_frame {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx : Cx} {env : Env} {tk : String} {r' : Idx} {o : Option (Proto × Idx)} {Rf : Res}
    (hi : FInvR ρ η σs K cx env Rf) (hcr : CohR η) (hpk : cx.peek (.var tk) = .ok (.tok r' o)) :
    1 ≤ Rf (.rg (ev ρ r')) ∧ Sat cx.facts ρ := by
  obtain ⟨c₁, hu, -⟩ := TermSpawnSim.use_var_true (peek_var hpk)
  obtain ⟨hle, hsat⟩ := TermLiveHeld.tok_frame hi hcr hu
  rw [(use_back hu).2.1] at hsat
  exact ⟨hle, hsat⟩

/-! ## The producers -/

/-- A plain store (static pointee word-free) never targets a runtime word reference. -/
theorem plain_store_not_word {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {a : At} {t u rt : Ty} {μ : Mode} {pw : Word} {ri : Idx} {P : Proto}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek a = .ok t) (hc : cellOf t = some (μ, u))
    (hwf : Ty.wordFreeIn cx.ke u = true) (hea : evalAt env a = some (rt, [pw])) (hwo : wordOf rt = some (ri, P)) :
    False := by
  obtain ⟨rt', ws, hea', -, hl⟩ := peek_VR hi.2.1 hpk
  rw [hea] at hea'
  cases hea'
  obtain ⟨r2, hcw⟩ := eskel_word (inv_runtime_word hl.2.1 hc hwo)
  have h := wordFree_close hi.2.2.2.2.2.1 u hwf
  rw [hcw] at h
  simp [Ty.wordFree, Ty.wordFreeIn] at h

/-- **Critical-section producer, scope (1).** For any invariant witness: thread `h` is on a `TokPath` to a
token store on a reference whose runtime pointee is a non-ghost word of `P` at `b`; `b`'s latest value is held;
no promise is outstanding.  Then `HeldBy … c b n P h` for the region `n` the witness's cell at `b` names. -/
theorem heldBy_of_tokpath {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c : Cfg}
    {Eg : GEnv} {Tot HP : Nat → TermSound.Res} {HS : TermSound.Res} {cr db : Nat → WeakMem.Ts → TermSound.Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    {h : Nat} {th : TTh} (hth : c.ths[h]? = some th)
    {a tk : String} (hte : TokPath a tk th.term = true)
    {rt : Ty} {pw : Word} {b : Address} (hea : evalAt th.env (.var a) = some (rt, [pw])) (hA : addrOf pw = some b)
    {ri : Idx} {P : Proto} (hwo : wordOf rt = some (ri, P)) (hg : P.ghost = false)
    {vv : WeakMem.Val} (hv : Latest c b vv) (hheld : TermLiveHeld.HeldV P vv) (hpf : AllNoProm c) :
    ∃ n, HeldBy p k arch Init c b n P h := by
  obtain ⟨S, hS⟩ := hN.thr h th hth
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, -, hE, hT, -, hFR, hRS, -, -, hH, -⟩ := TermMain.ThSysAt.env (S := S) hN.clo hS
  have hhs : h < c.ths.size := by
    rcases Nat.lt_or_ge h c.ths.size with h1 | h1
    · exact h1
    · simp [h1] at hth
  rcases typed_tokpath_inv hT.1 hte with ⟨t, r, r', i, P0, hpk, hwd, hpt, hrr⟩ | ⟨t, u, μ, hpk, hc, hwf⟩
  · obtain ⟨hle, hsat⟩ := peek_tok_frame hFR hE.2.2 hpt
    have he : ev ρ r = ev ρ r' := hrr ρ hsat
    obtain ⟨rt', ws, hea', -, hl⟩ := peek_VR hFR.1.2.1 hpk
    rw [hea] at hea'
    cases hea'
    obtain ⟨r'', hwt⟩ := inv_static_word hl.2.1 hwd
    rw [hwo] at hwt
    cases hwt
    obtain ⟨μ, hcell⟩ := inv_cell_of_word hwd
    obtain ⟨cl0, hsto, hat, hini⟩ := inv_target_cell hFR.1.2.1 hpk hcell (by simp [cl, accs, hg]) hea hA
    simp only [cl, clI_zero] at hat hini
    have hpwf : pwf P = true := inv_pwf_held hH hsto hat hini hat hg
    have h1 : (CE η).sto b.label = some cl0 := hsto
    rw [hCE, Cut_sto, cutSto_some] at h1
    refine ⟨ev ρ r, Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, ⟨cl0, h1.1, hat, hg⟩, fun cl hcl => ?_, hpwf,
      ⟨vv, hv, hheld⟩, hhs, ?_, debt_zero_of_allNoProm hpf db _⟩
    · rw [h1.1] at hcl
      cases hcl
      have hi2 : η.ini = Eg.ini := by
        have h3 := congrArg TEnv.ini hCE
        rw [Cut_ini] at h3
        exact h3
      rw [← hi2]
      exact hini
    · rw [← hRS, he]
      have := hle
      simp only [Res.add_apply]
      omega
  · exact (plain_store_not_word hFR.1 hpk hc hwf hea hwo).elim

/-- Every configuration of a `machineE` run from a `Setting` start carries an invariant witness. -/
theorem wit_of_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c₀ : Cfg}
    (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L} (hr : (machineE p k arch).Run r)
    (h0 : r.cfg 0 = c₀) (n : Nat) :
    ∃ Eg Tot HP HS cr db, SysInvN p k arch Init (fun _ => True) (r.cfg n) Eg Tot HP HS cr db ∧
      OwnLive Eg (r.cfg n) ∧ ObsAll Eg (r.cfg n) := by
  induction n with
  | zero => rw [h0]; exact S.start.1
  | succ n ih =>
    obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs⟩ := ih
    have hmv := hr n
    have hreach := machineE_run_stepsE hr n
    rw [h0] at hreach
    cases hl : r.lbl n with
    | none =>
      rw [hl] at hmv
      have he : r.cfg (n + 1) = r.cfg n := hmv
      rw [he]; exact ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs⟩
    | some l =>
      rw [hl] at hmv
      have hmv' : mstepE p k arch (r.cfg n) l (r.cfg (n + 1)) := hmv
      obtain ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, -⟩ :=
        sysInvO_mstepE_ext S hreach.1 hreach.2 hN hOL hObs hmv'
      exact ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3⟩


/-! ## Scope (2): the library-release endpoint -/

theorem peek_bind_self {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    c'.peek (.var x) = .ok t := by
  have he := bind_eq h
  subst he
  exact peek_of_find (y' := x) (List.find?_cons_of_pos (by simp))

theorem callEnd_inv {f mv tk x : String} {op : Op} {e : Expr} (h : callEnd f mv tk x op e = true) :
    ∃ y is ts e', op = .pair (.var mv) (.var tk) ∧ e = .let_ y (.call f is (.var x) ts) e' := by
  unfold callEnd at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, -⟩, -⟩ := h
    exact ⟨_, _, _, _, rfl, rfl⟩
  · simp at h

theorem unRefine_cases (t : Ty) : TermStartW.unRefine t = t ∨ ∃ t1 ψ, t = .refine t1 ψ := by
  cases t with
  | refine t1 ψ => exact .inr ⟨t1, ψ, rfl⟩
  | _ => exact .inl rfl

theorem unRefine_shiftI (c : Nat) (t : Ty) :
    TermStartW.unRefine (t.shiftI c) = (TermStartW.unRefine t).shiftI c := by
  induction t with
  | refine t ψ ih => simp only [Ty.shiftI, TermStartW.unRefine]; exact ih
  | _ => rfl

theorem VRR_unRefine {ρ : Nat → Nat} {η : TEnv} {S : Shp} {ws : List Word} {R : Res} :
    ∀ {t : Ty}, VRR ρ η t S ws R → VRR ρ η (TermStartW.unRefine t) S ws R := by
  intro t
  induction t with
  | refine t ψ ih => intro h; exact ih h.1
  | _ => intro h; exact h

theorem prodword_shiftI_inv {u c2 : Ty} {c : Nat} {r : Idx} {P : Proto}
    (h : u.shiftI c = .prod (.word r P) c2) :
    ∃ r0 c20, u = .prod (.word r0 P) c20 ∧ r = r0.shift c ∧ c2 = c20.shiftI c := by
  cases u with
  | prod a b =>
    cases a with
    | word r0 P0 =>
      simp only [Ty.shiftI, Ty.prod.injEq, Ty.word.injEq] at h
      obtain ⟨⟨h1, rfl⟩, h2⟩ := h
      exact ⟨r0, b, rfl, h1.symm, h2.symm⟩
    | _ => simp [Ty.shiftI] at h
  | _ => simp [Ty.shiftI] at h

theorem subS_prod_inv {cx : Cx} {a b a' b' : Ty} (h : SubS cx (.prod a b) (.prod a' b')) :
    SubS cx a a' ∧ SubS cx b b' := by
  cases h with
  | eq he =>
    cases he with
    | refl => exact ⟨.eq .refl, .eq .refl⟩
    | prod h1 h2 => exact ⟨.eq h1, .eq h2⟩
  | prod h1 h2 => exact ⟨h1, h2⟩

theorem subS_ptr_inv {cx : Cx} {t X : Ty} {μ : Mode} (h : SubS cx t (.ptr μ X)) :
    TyEqS cx 0 (TermStartW.unRefine t) (.ptr μ X) := by
  generalize hT : Ty.ptr μ X = T at h
  revert hT
  induction h with
  | eq he =>
    intro hT
    subst hT
    cases he with
    | refl => exact .refl
    | ptr h1 h2 => exact .ptr h1 h2
  | refine _ ih => intro hT; exact ih hT
  | _ => intro hT; cases hT

theorem subS_tok_inv {cx : Cx} {t : Ty} {I J : Idx} {P : Proto} (h : SubS cx t (.tok I (some (P, J)))) :
    ∃ s a, TermStartW.unRefine t = .tok s (some (P, a)) ∧ IEq cx 0 s I := by
  generalize hT : Ty.tok I (some (P, J)) = T at h
  revert hT
  induction h with
  | eq he =>
    intro hT
    subst hT
    cases he with
    | refl => exact ⟨I, J, rfl, .inl rfl⟩
    | tokSome h1 _ => exact ⟨_, _, rfl, h1⟩
  | refine _ ih => intro hT; exact ih hT
  | _ => intro hT; cases hT

theorem tyEqS_cellword_inv {cx : Cx} {T X : Ty} {I : Idx} {P : Proto}
    (h : TyEqS cx 0 T (.ptr .pub (.prod (.word I P) X))) :
    ∃ ν s b0, T = .ptr ν (.prod (.word s P) b0) ∧ IEq cx 0 s I := by
  cases h with
  | refl => exact ⟨_, _, _, rfl, .inl rfl⟩
  | ptr _ h2 =>
    cases h2 with
    | refl => exact ⟨_, _, _, rfl, .inl rfl⟩
    | prod h3 _ =>
      cases h3 with
      | refl => exact ⟨_, _, _, rfl, .inl rfl⟩
      | word hi => exact ⟨_, _, _, rfl, hi⟩

theorem ieq_comb {cx c : Cx} {s s' I : Idx} (hf : c.facts = cx.facts) (h1 : IEq c 0 s I)
    (h2 : IEq c 0 s' I) : EqI cx s s' := by
  intro ρ hs
  have hs' : Sat c.facts ρ := by rw [hf]; exact hs
  rcases h1 with rfl | ⟨-, h1⟩ <;> rcases h2 with rfl | ⟨-, h2⟩
  · rfl
  · exact (h2 ρ hs').symm
  · exact h1 ρ hs'
  · exact (h1 ρ hs').trans (h2 ρ hs').symm

/-- **Inversion, scope (2).** A typed term on a `TokPathCall` holds, at its own context, `mv` a cell (through
`refine`s) whose pointee is a pair headed by a word of `Pd` at `r`, and `tk` a token (through `refine`s)
`tok r' (Pd, i)`, with `r = r'` entailed (the callee's `argTy` subsumption). -/
theorem typed_tokpathcall_inv {p : Prog} {cx : Cx} {f mv tk : String} {e : Expr} {d : Decl}
    {Pd : Proto} {τd : Ty} {jd : Idx}
    (hT : Typed p cx e) (hp : TokPathCall f mv tk e = true) (hf : p.find f = .ok d)
    (hdt : d.tparams = [])
    (hda : d.argTy = .prod (cell Pd τd) (.tok (.var 0) (some (Pd, jd)))) :
    ∃ (t tt c2 : Ty) (μ : Mode) (r r' i : Idx), cx.peek (.var mv) = .ok t ∧
      cellOf (TermStartW.unRefine t) = some (μ, .prod (.word r Pd) c2) ∧ cx.peek (.var tk) = .ok tt ∧
      TermStartW.unRefine tt = .tok r' (some (Pd, i)) ∧ EqI cx r r' := by
  induction e generalizing cx with
  | let_ x op e ih =>
    cases hT with
    | let_ hop hT1 =>
      simp only [TokPathCall, Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with hend | ⟨hstep, hp⟩
      · obtain ⟨y, is, ts, e', rfl, rfl⟩ := callEnd_inv hend
        cases hop with
        | pair hu1 hu2 hb =>
          cases hT1 with
          | let_ hop2 _ =>
            cases hop2 with
            | call hf' hi hu3 _ hsub _ =>
              rw [hf] at hf'
              cases hf'
              obtain ⟨us, hlen, hat, -⟩ := instantiate_ok hi
              rw [hdt] at hlen
              have hts : ts = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
              subst hts
              rw [hda] at hat
              simp only [List.reverse_nil, substTs_nil', cell, instT, instM, Option.map_some] at hat
              subst hat
              have h3 := (use_cases hu3).1
              rw [peek_bind_self hb] at h3
              cases h3
              obtain ⟨hs1, hs2⟩ := subS_prod_inv hsub
              obtain ⟨ν, s, b0, hm, hi1⟩ := tyEqS_cellword_inv (subS_ptr_inv hs1)
              obtain ⟨s', a, htk, hi2⟩ := subS_tok_inv hs2
              have hfa : _ := ((use_back hu3).2.1.trans (bind_back hb).2.1).trans
                ((use_back hu2).2.1.trans (use_back hu1).2.1)
              exact ⟨_, _, b0, ν, s, s', a, (use_cases hu1).1, by rw [hm]; rfl,
                (use_back hu1).1 _ _ (use_cases hu2).1, htk, ieq_comb hfa hi1 hi2⟩
      · obtain ⟨hxa, hxt, hsafe⟩ := pathStep_inv hstep
        obtain ⟨hst, -⟩ := opT_stable hop hsafe
        obtain ⟨t, tt, c2, μ, r, r', i, hpa, hc, hpt, htk, hrr⟩ := ih hT1 hp
        rcases hst with ⟨hb, hf2⟩ | ⟨hb, hf2⟩
        · exact ⟨t, tt, c2, μ, r, r', i, hb mv t (Ne.symm hxa) hpa, hc, hb tk tt (Ne.symm hxt) hpt, htk,
            eqI_same hf2 hrr⟩
        · obtain ⟨t0, hpa0, rfl⟩ := hb mv t (Ne.symm hxa) hpa
          obtain ⟨t1, hpt0, rfl⟩ := hb tk tt (Ne.symm hxt) hpt
          rw [unRefine_shiftI] at hc htk
          obtain ⟨r1, i1, h1, rfl⟩ := tok_some_shiftI htk
          rw [cellOf_shiftI] at hc
          cases hc0 : cellOf (TermStartW.unRefine t0) with
          | none => rw [hc0] at hc; cases hc
          | some q =>
            rw [hc0] at hc
            obtain ⟨μ0, u0⟩ := q
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨-, hu0⟩ := hc
            obtain ⟨r0, c20, rfl, rfl, rfl⟩ := prodword_shiftI_inv hu0
            exact ⟨t0, t1, c20, μ0, r0, r1, i1, hpa0, hc0, hpt0, h1, eqI_unshift hf2 hrr⟩
  | _ => simp [TokPathCall] at hp

/-- `peek_tok_frame` through `refine`s. -/
theorem peek_tok_frameR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx : Cx} {env : Env} {tk : String} {tt : Ty} {r' : Idx} {o : Option (Proto × Idx)} {Rf : Res}
    (hi : FInvR ρ η σs K cx env Rf) (hcr : CohR η) (hpk : cx.peek (.var tk) = .ok tt)
    (hun : TermStartW.unRefine tt = .tok r' o) :
    1 ≤ Rf (.rg (ev ρ r')) ∧ Sat cx.facts ρ := by
  obtain ⟨c₁, hu, -⟩ := TermSpawnSim.use_var_true (peek_var hpk)
  obtain ⟨rt, ws, R, Rr, -, -, -, hv, hi1, hle⟩ := useR hu hi hcr
  have hv2 := VRR_unRefine hv
  rw [hun] at hv2
  refine ⟨TermLiveHeld.one_le_of_VRR_tok hv2 hle, ?_⟩
  have hs := hi1.1.1
  rw [(use_back hu).2.1] at hs
  exact hs

theorem etok_rf_ptr (X : Ty) (μ : Mode) (Y : Ty) : etok (rf X) ≠ .ptr μ Y := by
  cases X <;> simp [rf, etok]

theorem etok_rf_loc (X : Ty) (μ : Mode) (Y : Ty) : etok (rf X) ≠ .loc μ Y := by
  cases X <;> simp [rf, etok]

theorem heldBy_of_tokpathcall {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c : Cfg}
    {Eg : GEnv} {Tot HP : Nat → TermSound.Res} {HS : TermSound.Res} {cr db : Nat → WeakMem.Ts → TermSound.Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    {h : Nat} {th : TTh} (hth : c.ths[h]? = some th)
    {f mv tk : String} (hte : TokPathCall f mv tk th.term = true)
    {d : Decl} {Pd : Proto} {τd : Ty} {jd : Idx} (hf : p.find f = .ok d)
    (hdt : d.tparams = []) (hda : d.argTy = .prod (cell Pd τd) (.tok (.var 0) (some (Pd, jd))))
    {rt u c2 : Ty} {μ : Mode} {pw : Word} {b : Address} (hea : evalAt th.env (.var mv) = some (rt, [pw]))
    (hA : addrOf pw = some b) {ri : Idx} {P : Proto} (hcl : cellOf rt = some (μ, u))
    (hpr : unfold1 u = .prod (.word ri P) c2) (hg : P.ghost = false)
    {vv : WeakMem.Val} (hv : Latest c b vv) (hheld : TermLiveHeld.HeldV P vv) (hpf : AllNoProm c) :
    ∃ n, HeldBy p k arch Init c b n P h := by
  obtain ⟨S, hS⟩ := hN.thr h th hth
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, -, hE, hT, -, hFR, hRS, -, -, hH, -⟩ := TermMain.ThSysAt.env (S := S) hN.clo hS
  have hhs : h < c.ths.size := by
    rcases Nat.lt_or_ge h c.ths.size with h1 | h1
    · exact h1
    · simp [h1] at hth
  obtain ⟨t, tt, c20, μ0, r, r', i, hpk, hc, hpt, htk, hrr⟩ := typed_tokpathcall_inv hT.1 hte hf hdt hda
  obtain ⟨hle, hsat⟩ := peek_tok_frameR hFR hE.2.2 hpt htk
  have he : ev ρ r = ev ρ r' := hrr ρ hsat
  obtain ⟨rt', ws, hea', hvr, hl⟩ := peek_VR hFR.1.2.1 hpk
  rw [hea] at hea'
  cases hea'
  have htr : TermStartW.unRefine t = t := by
    rcases unRefine_cases t with h1 | ⟨t1, ψ, rfl⟩
    · exact h1
    · exfalso
      have hs := hl.2.1
      rcases cell_cases hcl with rfl | rfl <;> simp only [close, substTs, skel, etok] at hs
      · exact etok_rf_ptr _ _ _ hs.symm
      · exact etok_rf_loc _ _ _ hs.symm
  rw [htr] at hc
  have hP : P = Pd := by
    have hs := hl.2.1
    rcases cell_cases hc with rfl | rfl <;> rcases cell_cases hcl with rfl | rfl <;>
      rcases unfold1_prod_cases hpr with rfl | ⟨s, rfl⟩ <;> simp [close, substTs, skel, etok] at hs
    all_goals exact hs.2.1
  subst hP
  have hna : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 (.prod (.word r P) c20)) := fun n e hF => by
    have h1 := Fd_nonmu hF (fun b => by simp [cl])
    simp [cl] at h1
  obtain ⟨ad, cl0, hws, hsto, hat, -, hini⟩ := cell_target hc hna hvr
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have hb : b = ad := by
    simp only [addrOf, hws] at hA
    cases hA; rfl
  subst hb
  have hacc : accs (cl ρ η.wit 0 0 (.word r P)) ≠ none := by simp [cl, accs, hg]
  have hf0 : AtOff (cl ρ η.wit 0 0 (.prod (.word r P) c20)) 0 (cl ρ η.wit 0 0 (.word r P)) :=
    AtOff.fst (b := cl ρ η.wit 0 0 c20) (.here (Or.inl hacc))
  have hat0 : AtOff cl0.ty b.offset (cl ρ η.wit 0 0 (.word r P)) := by
    simpa using AtOff_trans hat hf0
  have hini0 : IniAt η.ini cl0 b (cl ρ η.wit 0 0 (.word r P)) := by
    have h1 := IniAt_trans (IniAt_mono (modeIni_le_ini _ _ _) hini) (fun n e h => by simp [cl] at h) hf0
    have hoa : offs b 0 = b := by cases b; rfl
    rw [hoa] at h1
    exact h1
  simp only [cl, clI_zero] at hat0 hini0
  have hpwf : pwf P = true := inv_pwf_held hH hsto hat0 hini0 hat0 hg
  have h1 : (CE η).sto b.label = some cl0 := hsto
  rw [hCE, Cut_sto, cutSto_some] at h1
  refine ⟨ev ρ r, Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, ⟨cl0, h1.1, hat0, hg⟩, fun cl hcl => ?_, hpwf,
    ⟨vv, hv, hheld⟩, hhs, ?_, debt_zero_of_allNoProm hpf db _⟩
  · rw [h1.1] at hcl
    cases hcl
    have hi2 : η.ini = Eg.ini := by
      have h3 := congrArg TEnv.ini hCE
      rw [Cut_ini] at h3
      exact h3
    rw [← hi2]
    exact hini0
  · rw [← hRS, he]
    have := hle
    simp only [Res.add_apply]
    omega
/-! ## C, critical-section form -/

/-- **C, critical-section form (scope 1).** A thread crashed anywhere on a straight-line `TokPath` to the token
release store of a held, non-ghost protocol word leaves every thread that keeps touching the word `StuckOnW`
on it (from a promise-free point on).
Allowed path steps include loads and plain stores to OTHER cells (see `opSafe`).
LIMITS: straight-line paths only (the `cas → ret` window inside `lock` stays open); no ticket-lock instance is
claimed (the release of a ticket lock is not a single token store; see `NoTicket` at TermMain:513); reachability open. -/
theorem forced_wait_in_critical_section {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res}
    {c₀ : Cfg} (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L} (hr : (machineE p k arch).Run r)
    (h0 : r.cfg 0 = c₀) {D : Nat → Option Nat} (hD : CrashOK (machineE p k arch) r D)
    {i h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀)
    {th : TTh} (hth : (r.cfg n₀).ths[h]? = some th)
    {a tk : String} (hte : TokPath a tk th.term = true)
    {rt : Ty} {pw : Word} {b : Address} (hea : evalAt th.env (.var a) = some (rt, [pw])) (hA : addrOf pw = some b)
    {ri : Idx} {P : Proto} (hwo : wordOf rt = some (ri, P)) (hg : P.ghost = false)
    {vv : WeakMem.Val} (hv : Latest (r.cfg n₀) b vv) (hheld : TermLiveHeld.HeldV P vv)
    (hpf : PromFreeFrom r n₀)
    (hs : Often (fun n => r.lbl n = some ((machineE p k arch).thr i)))
    (ht : Often (fun n => TouchesW (r.cfg n) i b)) :
    StuckOnW (machineE p k arch) r i b := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs⟩ := wit_of_run S hr h0 n₀
  obtain ⟨n, hH⟩ := heldBy_of_tokpath hN hOL hObs hth hte hea hA hwo hg hv hheld (hpf n₀ (Nat.le_refl _))
  exact forced_wait_held_thm p k arch Init c₀ S r D i b n P h m n₀ hr h0 hD hm hmn hH hpf hs ht

/-- **C, critical-section form (scope 2: library release).** As `forced_wait_in_critical_section`, the path
ending in `call f (pair mv tk)` for an `unlockD`-shaped `f`; the word is `mv`'s first component.
LIMITS: as above; additionally `unlockD`'s own `split`/`fld 0` steps (inside the callee frame) are not covered. -/
theorem forced_wait_in_critical_section_call {p : Prog} {k : Promises.Knobs} {arch : Arch}
    {Init : TermSound.Res} {c₀ : Cfg} (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L}
    (hr : (machineE p k arch).Run r) (h0 : r.cfg 0 = c₀) {D : Nat → Option Nat}
    (hD : CrashOK (machineE p k arch) r D) {i h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀)
    {th : TTh} (hth : (r.cfg n₀).ths[h]? = some th)
    {f mv tk : String} (hte : TokPathCall f mv tk th.term = true)
    {d : Decl} {Pd : Proto} {τd : Ty} {jd : Idx} (hf : p.find f = .ok d)
    (hdt : d.tparams = []) (hda : d.argTy = .prod (cell Pd τd) (.tok (.var 0) (some (Pd, jd))))
    {rt u c2 : Ty} {μ : Mode} {pw : Word} {b : Address} (hea : evalAt th.env (.var mv) = some (rt, [pw]))
    (hA : addrOf pw = some b) {ri : Idx} {P : Proto} (hcl : cellOf rt = some (μ, u))
    (hpr : unfold1 u = .prod (.word ri P) c2) (hg : P.ghost = false)
    {vv : WeakMem.Val} (hv : Latest (r.cfg n₀) b vv) (hheld : TermLiveHeld.HeldV P vv)
    (hpf : PromFreeFrom r n₀)
    (hs : Often (fun n => r.lbl n = some ((machineE p k arch).thr i)))
    (ht : Often (fun n => TouchesW (r.cfg n) i b)) :
    StuckOnW (machineE p k arch) r i b := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs⟩ := wit_of_run S hr h0 n₀
  obtain ⟨n, hH⟩ := heldBy_of_tokpathcall hN hOL hObs hth hte hf hdt hda hea hA hcl hpr hg hv hheld
    (hpf n₀ (Nat.le_refl _))
  exact forced_wait_held_thm p k arch Init c₀ S r D i b n P h m n₀ hr h0 hD hm hmn hH hpf hs ht

/-! ## Instances -/

/-- `unlockD`'s body after its `split` (the release form itself is a one-step `TokPath`). -/
def unlockAfterSplit : Expr :=
  match unlockD.body with
  | .split _ _ _ (.let_ _ _ e) => e
  | _ => .ret .unit

/-- `writeBody true true`'s successful-`cas` branch (fence, payload write, closing token store). -/
def seqWriteOk : Expr :=
  match writeBody true true with
  | .split _ _ _ (.let_ _ _ (.let_ _ _ (.parity _ _ (.let_ _ _ (.cas _ _ _ _ _ _ ok _)) _))) => ok
  | _ => .ret .unit

/-- `incrD`'s body after `t := lock m` (payload read/modify/write, then `unlock (m, t)`). -/
def incrAfterLock : Expr :=
  match incrD.body with
  | .let_ _ _ e => e
  | _ => .ret .unit

example : TokPath "w" "t" unlockAfterSplit = true := by decide
example : TokPath "w" "t" seqWriteOk = true := by decide
example : TokPathCall "unlock" "m" "t" incrAfterLock = true := by decide
example : mutexLib.find "unlock" = .ok unlockD := by rfl
/-- Negative: a step mentioning `tk` breaks the path. -/
example : TokPath "w" "t" (.let_ "z" (.atom (.var "t")) (.let_ "u" (.store true (.var "w") (.lit 0) (some (.var "t"))) (.ret .unit))) = false := by decide
/-- Negative: a release store to a different cell (`w2`) is not the endpoint. -/
example : TokPath "w" "t" (.let_ "u" (.store true (.var "w2") (.lit 0) (some (.var "t"))) (.ret .unit)) = false := by decide
/-- Negative: a loop (`tail`) is not a path. -/
example : TokPath "w" "t" (.tail "lock" ["r"] (.var "m")) = false := by decide
/-- Negative: a branch (`cas`) is not a path, even when its `ok` arm is. -/
example : TokPath "w" "t" (.cas true false (.var "w") (.lit 0) (.lit 1) "t" seqWriteOk (.ret .unit)) = false := by decide
/-- Negative (scope 2): a call step before the endpoint breaks the path. -/
example : TokPathCall "unlock" "m" "t" (.let_ "z" (.call "g" [] (.lit 0)) incrAfterLock) = false := by decide
/-- Negative: a call step breaks the path. -/
example : TokPath "w" "t" (.let_ "z" (.call "g" [] (.lit 0)) (.let_ "u" (.store true (.var "w") (.lit 0) (some (.var "t"))) (.ret .unit))) = false := by decide

/-- **Seqlock instance (scope 1).** A writer crashed between its successful `cas` and its closing store (counter
odd): every thread that keeps touching the counter is stuck on it.  LIMITS as `forced_wait_in_critical_section`. -/
theorem seqlock_forced_wait_in_critical_section {p : Prog} {k : Promises.Knobs} {arch : Arch}
    {Init : TermSound.Res} {c₀ : Cfg} (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L}
    (hr : (machineE p k arch).Run r) (h0 : r.cfg 0 = c₀) {D : Nat → Option Nat}
    (hD : CrashOK (machineE p k arch) r D) {i h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀)
    {th : TTh} (hth : (r.cfg n₀).ths[h]? = some th)
    {a tk : String} (hte : TokPath a tk th.term = true)
    {rt : Ty} {pw : Word} {b : Address} (hea : evalAt th.env (.var a) = some (rt, [pw])) (hA : addrOf pw = some b)
    {ri : Idx} (hwo : wordOf rt = some (ri, seqP)) {j : Nat} (hv : Latest (r.cfg n₀) b (.num (2 * j + 1)))
    (hpf : PromFreeFrom r n₀)
    (hs : Often (fun n => r.lbl n = some ((machineE p k arch).thr i)))
    (ht : Often (fun n => TouchesW (r.cfg n) i b)) :
    StuckOnW (machineE p k arch) r i b :=
  forced_wait_in_critical_section S hr h0 hD hm hmn hth hte hea hA hwo rfl hv (heldV_seqP_odd j) hpf hs ht

/-- **Mutex instance (scope 1).** A holder crashed at `unlockD`'s release store, or on any `TokPath` to a token
store on the lock word (lock word reads `1`).  LIMITS as `forced_wait_in_critical_section`. -/
theorem mutex_forced_wait_in_critical_section {p : Prog} {k : Promises.Knobs} {arch : Arch}
    {Init : TermSound.Res} {c₀ : Cfg} (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L}
    (hr : (machineE p k arch).Run r) (h0 : r.cfg 0 = c₀) {D : Nat → Option Nat}
    (hD : CrashOK (machineE p k arch) r D) {i h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀)
    {th : TTh} (hth : (r.cfg n₀).ths[h]? = some th)
    {a tk : String} (hte : TokPath a tk th.term = true)
    {rt : Ty} {pw : Word} {b : Address} (hea : evalAt th.env (.var a) = some (rt, [pw])) (hA : addrOf pw = some b)
    {ri : Idx} (hwo : wordOf rt = some (ri, mutexP)) (hv : Latest (r.cfg n₀) b (.num 1))
    (hpf : PromFreeFrom r n₀)
    (hs : Often (fun n => r.lbl n = some ((machineE p k arch).thr i)))
    (ht : Often (fun n => TouchesW (r.cfg n) i b)) :
    StuckOnW (machineE p k arch) r i b :=
  forced_wait_in_critical_section S hr h0 hD hm hmn hth hte hea hA hwo rfl hv heldV_mutexP_one hpf hs ht

/-- **lockD-style instance (scope 2).** A client crashed inside an `incrD`-style critical section (after
`t := lock m`, before `unlock (m, t)` is entered), `unlock` resolving to `unlockD`, lock word reading `1`.
LIMITS as `forced_wait_in_critical_section_call`. -/
theorem mutex_incr_forced_wait_in_critical_section {p : Prog} {k : Promises.Knobs} {arch : Arch}
    {Init : TermSound.Res} {c₀ : Cfg} (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L}
    (hr : (machineE p k arch).Run r) (h0 : r.cfg 0 = c₀) {D : Nat → Option Nat}
    (hD : CrashOK (machineE p k arch) r D) {i h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀)
    {th : TTh} (hth : (r.cfg n₀).ths[h]? = some th)
    {mv tk : String} (hte : TokPathCall "unlock" mv tk th.term = true) (hf : p.find "unlock" = .ok unlockD)
    {rt u c2 : Ty} {μ : Mode} {pw : Word} {b : Address} (hea : evalAt th.env (.var mv) = some (rt, [pw]))
    (hA : addrOf pw = some b) {ri : Idx} (hcl : cellOf rt = some (μ, u))
    (hpr : unfold1 u = .prod (.word ri mutexP) c2) (hv : Latest (r.cfg n₀) b (.num 1))
    (hpf : PromFreeFrom r n₀)
    (hs : Often (fun n => r.lbl n = some ((machineE p k arch).thr i)))
    (ht : Often (fun n => TouchesW (r.cfg n) i b)) :
    StuckOnW (machineE p k arch) r i b :=
  forced_wait_in_critical_section_call (Pd := mutexP) (τd := .int) (jd := .lit 1) S hr h0 hD hm hmn hth hte hf
    rfl rfl hea hA hcl hpr rfl hv heldV_mutexP_one hpf hs ht

end TermLiveC

#print axioms TermLiveC.heldV_mutexP_one
#print axioms TermLiveC.heldV_seqP_odd
#print axioms TermLiveC.peek_of_find
#print axioms TermLiveC.peek_vars
#print axioms TermLiveC.use_back
#print axioms TermLiveC.bind_back
#print axioms TermLiveC.push_back
#print axioms TermLiveC.fenceCx_keeps
#print axioms TermLiveC.stab_b
#print axioms TermLiveC.stab_ub
#print axioms TermLiveC.stab_uub
#print axioms TermLiveC.opT_stable
#print axioms TermLiveC.wordOf_shiftI
#print axioms TermLiveC.cellOf_shiftI
#print axioms TermLiveC.wordFreeIn_shiftI
#print axioms TermLiveC.tok_some_shiftI
#print axioms TermLiveC.eqI_unshift
#print axioms TermLiveC.eqI_same
#print axioms TermLiveC.tokEnd_inv
#print axioms TermLiveC.pathStep_inv
#print axioms TermLiveC.typed_tokpath_inv
#print axioms TermLiveC.peek_tok_frame
#print axioms TermLiveC.plain_store_not_word
#print axioms TermLiveC.heldBy_of_tokpath
#print axioms TermLiveC.wit_of_run
#print axioms TermLiveC.peek_bind_self
#print axioms TermLiveC.callEnd_inv
#print axioms TermLiveC.unRefine_cases
#print axioms TermLiveC.unRefine_shiftI
#print axioms TermLiveC.VRR_unRefine
#print axioms TermLiveC.prodword_shiftI_inv
#print axioms TermLiveC.subS_prod_inv
#print axioms TermLiveC.subS_ptr_inv
#print axioms TermLiveC.subS_tok_inv
#print axioms TermLiveC.tyEqS_cellword_inv
#print axioms TermLiveC.ieq_comb
#print axioms TermLiveC.typed_tokpathcall_inv
#print axioms TermLiveC.peek_tok_frameR
#print axioms TermLiveC.etok_rf_ptr
#print axioms TermLiveC.etok_rf_loc
#print axioms TermLiveC.heldBy_of_tokpathcall
#print axioms TermLiveC.forced_wait_in_critical_section
#print axioms TermLiveC.forced_wait_in_critical_section_call
#print axioms TermLiveC.seqlock_forced_wait_in_critical_section
#print axioms TermLiveC.mutex_forced_wait_in_critical_section
#print axioms TermLiveC.mutex_incr_forced_wait_in_critical_section
