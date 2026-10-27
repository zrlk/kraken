/-
**`main`'s return address has the phase anchor's phase** (AArch64): at
`h0_ofPlaceOK_setupFN`'s call of `main` (`mainCallWSF_ofHeld`'s `hpre`),
the call returns to `(setupMC sw).sp1`, and `fnCode2Of`'s `RaOk` asks for
the phase of `bareMC.e0 + 4`. The checked table `mainPhTabS` does not relate
the two, but the runtime's code check `rtCodeOkS` (A11) does, through the
order of the groups: `rtPass` takes them in program order, each at the
first label of its name, so `scc_rt_start`'s labels come before `.0_entry`
and those of `scc_rt_alloc_tcb`, `scc_rt_thread_init` and
`scc_rt_stack_take` after `.sp1`. Every range of the phase table (`bPR`,
`bLR`, `bNR`, `bTR`) ends at one of the former or starts at one of the
latter, so `.0_entry + 4` and `.sp1` are in the same ranges.

- `rtPass_ord`: the groups' first labels at increasing indices (`OrdAll`),
  the order `rtPass` checks and `rtPass_sound` does not expose;
- `codeOf_eq`: `codeOf` through `labelIdx` and the sizes before (`sz`);
- `phOf_eq`: two pcs with no range of the phase table between them have
  the same phase;
- `ph_sp1_of_rtCodeOkS`: `.sp1`'s phase is `.0_entry + 4`'s, both in the
  address space;
- `raOk_main`: the same at the record `RuntimeLayout.ofPlaceOK`, in
  `fnCode2Of`'s `RaOk` form.
-/
import Spike.Lib.Rt.A64RtPhRec
import Spike.Lib.LowerA64.SetupOfPlaceOK

namespace Spike.Lib.LowerA64.RaMain

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (RGrp rtPass rtStep labelIdx key memR_iff key_inj labelIdx_append labelIdx_head
  RtAll BsOk blockAt run isIns rtIn_sound labelIdx_spec PhRange bPR bLR bNR bTR inRs phOf phTabOf phTabBy)
open Scc.Cert.Link.A64 (codeOf)

/-! ## The order of the groups -/

/-- **The groups' first labels at increasing indices**, from `n` on. -/
def OrdAll (prog : List Directive) : Nat → List RGrp → Prop
  | _, [] => True
  | n, g :: gs => ∃ i, n ≤ i ∧ labelIdx prog g.l = some i ∧ OrdAll prog (i + 1) gs

theorem OrdAll.mono {prog : List Directive} : ∀ {n m : Nat} {gs : List RGrp}, m ≤ n →
    OrdAll prog n gs → OrdAll prog m gs
  | _, _, [], _, _ => trivial
  | _, _, _ :: _, hm, ⟨i, hi, h1, h2⟩ => ⟨i, by omega, h1, h2⟩

/-- A group's first label at an index from `n` on. -/
theorem OrdAll.mem {prog : List Directive} : ∀ {n : Nat} {gs : List RGrp}, OrdAll prog n gs →
    ∀ g ∈ gs, ∃ i, n ≤ i ∧ labelIdx prog g.l = some i
  | _, [], _, _, hg => nomatch hg
  | _, _ :: _, ⟨i, hi, h1, h2⟩, g, hg => by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨i, hi, h1⟩
    · obtain ⟨j, hj, h⟩ := OrdAll.mem h2 g hg
      exact ⟨j, by omega, h⟩

/-- The groups before `ys` at indices below some `m`, those of `ys` from `m`. -/
theorem OrdAll.append {prog : List Directive} : ∀ {n : Nat} {xs ys : List RGrp}, OrdAll prog n (xs ++ ys) →
    ∃ m, n ≤ m ∧ OrdAll prog m ys ∧ ∀ g ∈ xs, ∃ i, i < m ∧ labelIdx prog g.l = some i
  | n, [], _, h => ⟨n, Nat.le_refl _, h, fun _ hg => nomatch hg⟩
  | _, _ :: _, _, ⟨i, hi, h1, h2⟩ => by
    obtain ⟨m, hm, hy, hx⟩ := OrdAll.append h2
    refine ⟨m, by omega, hy, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨i, by omega, h1⟩
    · exact hx g hg

/-- **The order `rtPass` checks**: its groups' first labels at increasing
indices after the directives `pre` already passed. -/
theorem rtPass_ord : ∀ (s pre : List Directive) (seen : List Nat) (gs : List RGrp),
    (∀ m, Directive.label m ∈ pre → key m ∈ seen) → rtPass s seen gs = true → OrdAll (pre ++ s) pre.length gs
  | [], _, _, gs, _, h => by
    cases gs with
    | nil => trivial
    | cons _ _ => cases h
  | d :: ds, pre, seen, gs, hpre, h => by
    have ih := rtPass_ord ds (pre ++ [d])
    have happ : pre ++ [d] ++ ds = pre ++ d :: ds := by simp
    have hlen : (pre ++ [d]).length = pre.length + 1 := by simp
    rw [← happ]
    change rtStep d ds (rtPass ds) seen gs = true at h
    unfold rtStep at h
    split at h
    next => trivial
    next g gs' =>
      split at h
      next m =>
        have hpre' : ∀ m', Directive.label m' ∈ pre ++ [.label m] → key m' ∈ key m :: seen := by
          intro m' hm'
          rcases List.mem_append.mp hm' with hm' | hm'
          · exact List.mem_cons_of_mem _ (hpre m' hm')
          · simp only [List.mem_singleton, Directive.label.injEq] at hm'; simp [hm']
        cases hk : Nat.beq (key m) (key g.l)
        · rw [hk, Bool.cond_false] at h
          exact (ih _ _ hpre' h).mono (by simp)
        · rw [hk, Bool.cond_true] at h
          have hm : m = g.l := key_inj (Nat.beq_eq_true_eq _ _ ▸ hk)
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
          obtain ⟨⟨⟨hs, -⟩, -⟩, hr⟩ := h
          have hnm : Directive.label m ∉ pre := fun hl => by
            have := memR_iff.mpr (hpre _ hl); simp [this] at hs
          refine ⟨pre.length, Nat.le_refl _, ?_, ?_⟩
          · rw [← hm, happ, labelIdx_append _ hnm, labelIdx_head]; simp
          · have := ih _ _ hpre' hr
            simpa using this
      next hnl =>
        refine (ih _ _ ?_ h).mono (by simp)
        intro m' hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact hpre m' hm'
        · simp only [List.mem_singleton] at hm'; exact absurd hm'.symm (hnl m')

/-! ## Addresses -/

/-- The bytes of a list of directives. -/
def sz (xs : List Directive) : Nat := (xs.map Directive.fakeSize).sum

theorem sz_take_succ (prog : List Directive) (m : Nat) :
    sz (prog.take (m + 1)) = sz (prog.take m) + (prog[m]?.map Directive.fakeSize).getD 0 := by
  rw [List.take_add_one]; cases prog[m]? <;> simp [sz]

theorem sz_mono (prog : List Directive) {i j : Nat} (h : i ≤ j) : sz (prog.take i) ≤ sz (prog.take j) := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [sz_take_succ]; omega

theorem sz_ins (prog : List Directive) (i : Nat) : ∀ {n : Nat}, (∀ t < n, ∃ x, prog[i + t]? = some (.instr x)) →
    sz (prog.take (i + n)) = sz (prog.take i) + 4 * n
  | 0, _ => by simp
  | n + 1, h => by
    rw [← Nat.add_assoc, sz_take_succ, sz_ins prog i (fun t ht => h t (by omega))]
    obtain ⟨x, hx⟩ := h n (by omega)
    rw [hx]; simp [Directive.fakeSize]; omega

/-- The bytes up to an index at most those of the whole list. -/
theorem sz_le (prog : List Directive) (j : Nat) : sz (prog.take j) ≤ sz prog := by
  have := sz_mono prog (Nat.le_max_left j prog.length)
  rwa [List.take_of_length_le (Nat.le_max_right j prog.length)] at this

/-- A label after an instruction after the label at `i`: `4` bytes more. -/
theorem sz_after {prog : List Directive} {i j : Nat} {l : Label} {x : Instr} (hj : labelIdx prog l = some j)
    (hx : prog[i + 1]? = some (.instr x)) (hij : i < j) : sz (prog.take i) + 4 ≤ sz (prog.take j) := by
  have hne : j ≠ i + 1 := fun e => by
    have := (labelIdx_spec hj).1; rw [e, hx] at this; cases this
  have h1 := sz_mono prog (show i ≤ i + 1 by omega)
  have h2 := sz_ins prog (i + 1) (n := 1) (fun t ht => ⟨x, by rw [show t = 0 by omega]; exact hx⟩)
  have h3 := sz_mono prog (show i + 1 + 1 ≤ j by omega)
  omega

/-- `k + 1` instructions after the label at `i`: at least `4 (k + 1)` bytes
after it. -/
theorem sz_run {prog : List Directive} {i k : Nat} (h : ∀ t ≤ k, ∃ x, prog[i + 1 + t]? = some (.instr x)) :
    sz (prog.take i) + 4 * (k + 1) ≤ sz prog := by
  have h1 := sz_mono prog (show i ≤ i + 1 by omega)
  have h2 := sz_ins prog (i + 1) (n := k + 1) (fun t ht => h t (by omega))
  have h3 := sz_le prog (i + 1 + (k + 1))
  omega

/-- **`codeOf` through `labelIdx`**: a label's address is the code base
plus the bytes before its first occurrence. -/
theorem codeOf_eq : ∀ (prog : List Directive) (base : Nat) (l : String),
    codeOf base prog l = (labelIdx prog l).map fun i => base + sz (prog.take i)
  | [], _, _ => rfl
  | d :: ds, base, l => by
    simp only [codeOf, Scc.Sem.labelAddr, labelIdx]
    by_cases hd : d = .label l
    · subst hd; simp [Scc.Sem.A64.labelName, sz]
    · have h1 : Scc.Sem.A64.labelName d ≠ some l := by cases d <;> simp_all [Scc.Sem.A64.labelName]
      have ih := codeOf_eq ds (base + d.fakeSize) l
      simp only [codeOf] at ih
      simp only [h1, hd, ↓reduceIte, ih, Option.map_map]
      congr 1; funext i; simp [sz]; omega

/-- A block at `k` names instructions `0` … `k` after its label. -/
theorem ins_of_blockAt {prog : List Directive} {l : Label} {k : Nat} {b : List Directive}
    (h : blockAt prog l k b = true) (hb : b ≠ []) :
    ∃ i, labelIdx prog l = some i ∧ ∀ t ≤ k, ∃ x, prog[i + 1 + t]? = some (.instr x) := by
  unfold blockAt run at h
  cases hi : labelIdx prog l with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, Option.isSome_some, Bool.true_and, decide_eq_true_eq] at h
    refine ⟨i, rfl, fun t ht => ?_⟩
    have hlen : k < ((prog.drop (i + 1)).takeWhile isIns).length := by
      apply Classical.byContradiction
      intro hc
      rw [List.drop_eq_nil_of_le (by omega)] at h
      exact hb (by simpa using h.symm)
    have hmem := List.getElem_mem (l := (prog.drop (i + 1)).takeWhile isIns) (n := t) (by omega)
    have hins := List.all_eq_true.mp (List.all_takeWhile (p := isIns) (l := prog.drop (i + 1))) _ hmem
    have hget : prog[i + 1 + t]? = some ((prog.drop (i + 1)).takeWhile isIns)[t] := by
      rw [← List.getElem?_eq_getElem, ← List.getElem?_drop]
      conv => lhs; rw [← List.takeWhile_append_dropWhile (p := isIns) (l := prog.drop (i + 1))]
      rw [List.getElem?_append_left (by omega)]
    rw [hget]
    revert hins
    cases ((prog.drop (i + 1)).takeWhile isIns)[t] <;> simp [isIns]

/-! ## Phases -/

theorem mem_of_mapM {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
    ∀ p ∈ l', ∃ r ∈ l, f r = some p
  | [], l', h, p, hp => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; cases hp
  | a :: l, l', h, p, hp => by
    simp only [List.mapM_cons, bind, pure] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨r, hr, e⟩ := mem_of_mapM hl p hp
          exact ⟨r, List.mem_cons_of_mem _ hr, e⟩

theorem inRs_eq {a0 a1 : Nat} (hle : a0 ≤ a1) : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.2 ≤ a0 ∨ a1 < r.1) →
    inRs rs a1 = inRs rs a0
  | [], _ => rfl
  | r :: rs, h => by
    have ih := inRs_eq hle (rs := rs) (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    have hr := h r List.mem_cons_self
    simp only [inRs, List.any_cons] at ih ⊢
    rw [ih]
    congr 1
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **Two pcs with no range of the phase table between them** have the
same phase. -/
theorem phOf_eq {lo : Nat} {prog : List Directive} {a0 a1 : Nat} (hle : a0 ≤ a1)
    (hr : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, ∀ x y, r.resolve (codeOf lo prog) = some (x, y) → y ≤ a0 ∨ a1 < x) :
    phOf lo prog a1 = phOf lo prog a0 := by
  have hr' : ∀ (rs : List PhRange) (rs' : List (Nat × Nat)), (∀ r ∈ rs, r ∈ bPR ++ bLR ++ bNR ++ bTR) →
      rs.mapM (PhRange.resolve (codeOf lo prog)) = some rs' → inRs rs' a1 = inRs rs' a0 :=
    fun rs rs' hsub hm => inRs_eq hle fun p hp => by
      obtain ⟨r, hr0, e⟩ := mem_of_mapM hm p hp
      exact hr r (hsub r hr0) p.1 p.2 e
  unfold phOf phTabOf phTabBy
  cases hp : bPR.mapM (PhRange.resolve (codeOf lo prog)) with
  | none => simp [bind]
  | some p =>
    cases hl : bLR.mapM (PhRange.resolve (codeOf lo prog)) with
    | none => simp [bind]
    | some l =>
      cases hn : bNR.mapM (PhRange.resolve (codeOf lo prog)) with
      | none => simp [bind]
      | some n =>
        cases ht : bTR.mapM (PhRange.resolve (codeOf lo prog)) with
        | none => simp [bind]
        | some t =>
          simp only [bind, pure, Option.bind_some]
          simp only [Scc.Cert.Rt.A64.PhTab.ph]
          rw [hr' _ _ (fun r hr => by simp [hr]) hp, hr' _ _ (fun r hr => by simp [hr]) hl,
            hr' _ _ (fun r hr => by simp [hr]) hn, hr' _ _ (fun r hr => by simp [hr]) ht]

/-- A range ending at a label at or below `a0`, with no offset, ends at or
below `a0`. -/
theorem resolve_before {code : String → Option Nat} {l1 l2 : String} {o1 c a0 x y : Nat} (hc : code l2 = some c)
    (hlt : c < 2 ^ 64) (hle : c ≤ a0) (he : PhRange.resolve code ⟨l1, o1, l2, 0⟩ = some (x, y)) : y ≤ a0 := by
  unfold PhRange.resolve at he
  split at he
  next a b _ e2 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    have : b = c := Option.some.inj (e2.symm.trans hc)
    rw [← he.2, this, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hlt]; exact hle
  next => cases he

/-- A range starting at a label above `a1`, its offset in the address
space, starts above `a1`. -/
theorem resolve_after {code : String → Option Nat} {l1 l2 : String} {o1 o2 c a1 x y : Nat} (hc : code l1 = some c)
    (hlt : c + 4 * o1 < 2 ^ 64) (hlt1 : a1 < c) (he : PhRange.resolve code ⟨l1, o1, l2, o2⟩ = some (x, y)) :
    a1 < x := by
  unfold PhRange.resolve at he
  split at he
  next a b e1 _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    have : a = c := Option.some.inj (e1.symm.trans hc)
    rw [← he.1, this, Nat.mod_eq_of_lt hlt]; omega
  next => cases he

section Main

open Spike.Lib.A64.Rt (SetupCode rtCodeOkS rtCodeTabS startGrps mainSGrps tcbGrps tiGrps takeGrps)
open Spike.Lib.A64.Rt.Code

/-- **The phase table at two pcs** `a0 ≤ a1`: `scc_rt_start`'s `.sp2` and
`.sp3` at or below `a0`, the labels of `scc_rt_alloc_tcb`,
`scc_rt_thread_init`, `scc_rt_stack_take` and its spin above `a1`. -/
theorem phOf_eq_of {lo : Nat} {prog : List Directive} {a0 a1 c2 c3 ct ci ck cs : Nat} (hle : a0 ≤ a1)
    (h2 : codeOf lo prog Start.sp2L = some c2) (h3 : codeOf lo prog Start.sp3L = some c3)
    (h2' : c2 ≤ a0) (h3' : c3 ≤ a0) (ha0 : a0 < 2 ^ 64)
    (ht : codeOf lo prog Tcb.fnL = some ct) (hi : codeOf lo prog Ti.fnL = some ci)
    (hk : codeOf lo prog Take.fnL = some ck) (hs : codeOf lo prog Take.spinL = some cs)
    (ht' : a1 < ct) (hi' : a1 < ci) (hk' : a1 < ck) (hs' : a1 < cs) (hct : ct < 2 ^ 64) (hci : ci < 2 ^ 64)
    (hck : ck < 2 ^ 64) (hcs : cs + 12 < 2 ^ 64) :
    phOf lo prog a1 = phOf lo prog a0 := by
  refine phOf_eq hle fun r hr x y he => ?_
  simp only [bPR, bLR, bNR, bTR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inl (resolve_before h2 (by omega) h2' he)
    | exact .inl (resolve_before h3 (by omega) h3' he)
    | exact .inr (resolve_after ht (by omega) ht' he)
    | exact .inr (resolve_after hi (by omega) hi' he)
    | exact .inr (resolve_after hk (by omega) hk' he)
    | exact .inr (resolve_after hs (by omega) hs' he)

/-- **`.sp1`'s phase is `.0_entry + 4`'s** in a program passing the
runtime's code check after a setup block at `sc` (`rtCodeOkS`), its code in
the address space: both resolve, `.0_entry + 4` at or below `.sp1`. -/
theorem ph_sp1_of_rtCodeOkS {lo : Nat} {prog : List Directive} {sc : SetupCode}
    (hc : rtCodeOkS prog sc = true) (hend : Scc.Sem.A64.codeEnd lo prog < 2 ^ 64) :
    ∃ a a1, codeOf lo prog sc.e0 = some a ∧ codeOf lo prog sc.sp1 = some a1 ∧ a + 4 ≤ a1 ∧ a1 < 2 ^ 64 ∧
      phOf lo prog a1 = phOf lo prog (a + 4) := by
  have hend' : lo + sz prog < 2 ^ 64 := hend
  have hord : OrdAll prog 0 (rtCodeTabS sc) := by
    simpa using rtPass_ord prog [] [] _ (by simp) hc
  have hall : RtAll prog (rtCodeTabS sc) := rtIn_sound hc
  simp only [rtCodeTabS, List.append_assoc] at hord hall
  obtain ⟨m0, -, hord, hst⟩ := OrdAll.append hord
  have hall2 := (Scc.Cert.Rt.A64.RtAll.append hall).2
  have hmain := (Scc.Cert.Rt.A64.RtAll.append hall2).1
  have htake := (Scc.Cert.Rt.A64.RtAll.append (Scc.Cert.Rt.A64.RtAll.append
    (Scc.Cert.Rt.A64.RtAll.append hall2).2).2).2
  obtain ⟨-, -, -, -, ⟨he0b, -⟩, -, -, -, ⟨hsp1b, -⟩, -, -⟩ := hmain
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, hspb, -⟩, -, -⟩ := htake
  rw [mainSGrps, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append] at hord
  obtain ⟨i1, hi1, -, i2, hi2, -, i3, hi3, he0i, i4, hi4, -, i5, hi5, hsp1i, hrest⟩ := hord
  obtain ⟨i3', he0i', he0n⟩ := ins_of_blockAt he0b (List.cons_ne_nil _ _)
  obtain ⟨i5', hsp1i', hsp1n⟩ := ins_of_blockAt hsp1b (List.cons_ne_nil _ _)
  obtain ⟨js, hjs, hspn⟩ := ins_of_blockAt hspb (by simp [Take.stSpin])
  rw [he0i] at he0i'; cases he0i'
  rw [hsp1i] at hsp1i'; cases hsp1i'
  obtain ⟨x5, hx5⟩ := hsp1n 0 (Nat.zero_le _)
  obtain ⟨x3, hx3⟩ := he0n 0 (Nat.zero_le _)
  have hcode : ∀ {l : Label} {j : Nat}, labelIdx prog l = some j → codeOf lo prog l = some (lo + sz (prog.take j)) :=
    fun h => by rw [codeOf_eq, h]; rfl
  -- the labels before
  obtain ⟨j2, hj2, hl2⟩ := hst ⟨Start.sp2L, _, _⟩ (List.getElem_mem (l := startGrps) (n := 3) (by decide))
  obtain ⟨j3, hj3, hl3⟩ := hst ⟨Start.sp3L, _, _⟩ (List.getElem_mem (l := startGrps) (n := 4) (by decide))
  -- the labels after
  have hmem : ∀ g ∈ tcbGrps ++ (tiGrps ++ takeGrps), ∃ j, i5 + 1 ≤ j ∧ labelIdx prog g.l = some j :=
    OrdAll.mem hrest
  obtain ⟨jt, hjt, hlt⟩ := hmem ⟨Tcb.fnL, _, _⟩ (List.mem_append_left _ (List.getElem_mem (l := tcbGrps) (n := 0)
    (by decide)))
  obtain ⟨ji, hji, hli⟩ := hmem ⟨Ti.fnL, _, _⟩ (List.mem_append_right _ (List.mem_append_left _
    (List.getElem_mem (l := tiGrps) (n := 0) (by decide))))
  obtain ⟨jk, hjk, hlk⟩ := hmem ⟨Take.fnL, _, _⟩ (List.mem_append_right _ (List.mem_append_right _
    (List.getElem_mem (l := takeGrps) (n := 0) (by decide))))
  obtain ⟨jsp, hjsp, hlsp⟩ := hmem ⟨Take.spinL, _, _⟩ (List.mem_append_right _ (List.mem_append_right _
    (List.getElem_mem (l := takeGrps) (n := 4) (by decide))))
  have hjj : jsp = js := Option.some.inj (hlsp.symm.trans hjs)
  subst hjj
  -- the bytes
  have e1 := sz_after hsp1i hx3 (show i3 < i5 by omega)
  have e2 := sz_le prog i5
  have e3 := sz_mono prog (show j2 ≤ i3 by omega)
  have e4 := sz_mono prog (show j3 ≤ i3 by omega)
  have e5 := sz_after hlt hx5 (show i5 < jt by omega)
  have e6 := sz_after hli hx5 (show i5 < ji by omega)
  have e7 := sz_after hlk hx5 (show i5 < jk by omega)
  have e8 := sz_after hlsp hx5 (show i5 < jsp by omega)
  have e9 := sz_le prog jt
  have e10 := sz_le prog ji
  have e11 := sz_le prog jk
  have e12 := sz_run (k := 3) hspn
  refine ⟨_, _, hcode he0i, hcode hsp1i, by omega, by omega, ?_⟩
  exact phOf_eq_of (by omega) (hcode hl2) (hcode hl3) (by omega) (by omega) (by omega) (hcode hlt) (hcode hli)
    (hcode hlk) (hcode hlsp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

end Main

section Rec

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout setupMC bareMC rtCodeOkS)

/-- **`main`'s return address has the phase anchor's phase**
(`fnCode2Of`'s `RaOk` at `(setupMC sw).sp1`) at the record of an output
passing `placeOK` whose runtime's code holds at `setupMC sw` (A11,
`setupIn_of_placeOKAt`). -/
theorem raOk_main {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {sw : Nat} (hc : rtCodeOkS o.prog (setupMC sw) = true) :
    Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)
        (Int64.ofBitVec ((RuntimeLayout.ofPlaceOK h i).lab (setupMC sw).sp1).toBitVec).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)
        (Int64.ofBitVec ((RuntimeLayout.ofPlaceOK h i).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat := by
  obtain ⟨a, a1, ha, ha1, hle, hlt, hph⟩ := ph_sp1_of_rtCodeOkS hc (Spike.Lib.A64.PhRec.codeEnd_lt h i)
  have l0 := Spike.Lib.A64.Rt.PhRecOf.hlab_ofPlaceOK h i _ _ ha
  have l1 := Spike.Lib.A64.Rt.PhRecOf.hlab_ofPlaceOK h i _ _ ha1
  show phOf _ _ _ = phOf _ _ _
  rw [show bareMC.e0 = (setupMC sw).e0 from rfl, l0, l1]
  have e0 : (Int64.ofNat a + 4) = Int64.ofNat (a + 4) := by rw [Int64.ofNat_add]; rfl
  rw [e0]
  have t1 : (Int64.ofNat a1).toBitVec.toNat = a1 := by simp [Nat.mod_eq_of_lt hlt]
  have t0 : (Int64.ofNat (a + 4)).toBitVec.toNat = a + 4 := by
    simp [Nat.mod_eq_of_lt (show a + 4 < 2 ^ 64 by omega)]
  simp only [Int64.ofBitVec_toBitVec, t0, t1]
  exact hph

end Rec

/-- info: 'Spike.Lib.LowerA64.RaMain.OrdAll.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdAll.mono

/-- info: 'Spike.Lib.LowerA64.RaMain.OrdAll.mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdAll.mem

/-- info: 'Spike.Lib.LowerA64.RaMain.OrdAll.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdAll.append

/-- info: 'Spike.Lib.LowerA64.RaMain.rtPass_ord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rtPass_ord

/-- info: 'Spike.Lib.LowerA64.RaMain.sz_take_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms sz_take_succ

/-- info: 'Spike.Lib.LowerA64.RaMain.sz_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_mono

/-- info: 'Spike.Lib.LowerA64.RaMain.sz_ins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_ins

/-- info: 'Spike.Lib.LowerA64.RaMain.sz_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_le

/-- info: 'Spike.Lib.LowerA64.RaMain.sz_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_after

/-- info: 'Spike.Lib.LowerA64.RaMain.sz_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_run

/-- info: 'Spike.Lib.LowerA64.RaMain.codeOf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms codeOf_eq

/-- info: 'Spike.Lib.LowerA64.RaMain.ins_of_blockAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ins_of_blockAt

/-- info: 'Spike.Lib.LowerA64.RaMain.mem_of_mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_of_mapM

/-- info: 'Spike.Lib.LowerA64.RaMain.inRs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inRs_eq

/-- info: 'Spike.Lib.LowerA64.RaMain.phOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms phOf_eq

/-- info: 'Spike.Lib.LowerA64.RaMain.resolve_before' depends on axioms: [propext] -/
#guard_msgs in #print axioms resolve_before

/-- info: 'Spike.Lib.LowerA64.RaMain.resolve_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resolve_after

/-- info: 'Spike.Lib.LowerA64.RaMain.phOf_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms phOf_eq_of

/-- info: 'Spike.Lib.LowerA64.RaMain.ph_sp1_of_rtCodeOkS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ph_sp1_of_rtCodeOkS

/-- info: 'Spike.Lib.LowerA64.RaMain.raOk_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms raOk_main

end Spike.Lib.LowerA64.RaMain
