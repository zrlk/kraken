/-
**`main`'s return address has the phase anchor's phase** (x86-64; the twin
of `Spike/Lib/LowerA64/RaMain2.lean`): at `h0_ofPlaceOK_setupFN`'s call of
`main` (`mainCallWSF_ofHeld`'s `hpre`), the call returns to
`(setupMC sw).sp1`, and `fnCode2Of`'s `RaOk` asks for the phase of `raL`
(`.x2`, `(setupMC sw).sp0`). The checked table `mainPhTabS` does not relate
the two, but the runtime's code check `rtCodeOkS` (A11) does, through the
order of the groups: `rtPass` takes them in program order, each at the
first label of its name, so `scc_rt_start`'s labels come before `.x2` and
those of `scc_rt_alloc_tcb`, `scc_rt_thread_init` and `scc_rt_stack_take`
after `.x3`. Every range of the phase table (`bPR`, `bLR`, `bNR`, `bTR`)
ends at one of the former or starts at one of the latter, so `.x2` and
`.x3` are in the same ranges.

- `rtPass_ord`: the groups' first labels at increasing indices (`OrdAll`),
  the order `rtPass` checks and `rtPass_sound` does not expose;
- `codeLabel_eq`: `codeLabel` through `labelIdx` and the sizes before
  (`sz`);
- `phOf_eq`: two pcs with no range of the phase table between them have
  the same phase;
- `ph_sp1_of_rtCodeOkS`: `.x3`'s phase is `.x2`'s, both in the address
  space;
- `raOk_main`: the same at the record `RuntimeLayout.ofPlaceOK`, in
  `fnCode2Of`'s `RaOk` form.
-/
import Spike.Lib.Rt.X64RtPhRec
import Spike.Lib.LowerX64.PhCheck

namespace Spike.Lib.LowerX64.RaMain

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (RGrp rtPass rtStep labelIdx key memR_iff key_inj labelIdx_append_of labelIdx_head
  RtAll BsOk blockAtB rtIn_sound labelIdx_spec PhRange bPR bLR bNR bTR inRs phOf phTabOf phTabBy
  after_eq cellRun cellRun_append_runRest dropBytes_sound notLab)
open Scc.Sem.X64 (codeLabel)

/-! ## The order of the groups -/

/-- **The groups' first labels at increasing indices**, from `n` on. -/
def OrdAll (cells : List (Directive × Nat)) : Nat → List RGrp → Prop
  | _, [] => True
  | n, g :: gs => ∃ i, n ≤ i ∧ labelIdx cells g.l = some i ∧ OrdAll cells (i + 1) gs

theorem OrdAll.mono {cells : List (Directive × Nat)} : ∀ {n m : Nat} {gs : List RGrp}, m ≤ n →
    OrdAll cells n gs → OrdAll cells m gs
  | _, _, [], _, _ => trivial
  | _, _, _ :: _, hm, ⟨i, hi, h1, h2⟩ => ⟨i, by omega, h1, h2⟩

/-- A group's first label at an index from `n` on. -/
theorem OrdAll.mem {cells : List (Directive × Nat)} : ∀ {n : Nat} {gs : List RGrp}, OrdAll cells n gs →
    ∀ g ∈ gs, ∃ i, n ≤ i ∧ labelIdx cells g.l = some i
  | _, [], _, _, hg => nomatch hg
  | _, _ :: _, ⟨i, hi, h1, h2⟩, g, hg => by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨i, hi, h1⟩
    · obtain ⟨j, hj, h⟩ := OrdAll.mem h2 g hg
      exact ⟨j, by omega, h⟩

/-- The groups before `ys` at indices below some `m`, those of `ys` from `m`. -/
theorem OrdAll.append {cells : List (Directive × Nat)} : ∀ {n : Nat} {xs ys : List RGrp},
    OrdAll cells n (xs ++ ys) →
    ∃ m, n ≤ m ∧ OrdAll cells m ys ∧ ∀ g ∈ xs, ∃ i, i < m ∧ labelIdx cells g.l = some i
  | n, [], _, h => ⟨n, Nat.le_refl _, h, fun _ hg => nomatch hg⟩
  | _, _ :: _, _, ⟨i, hi, h1, h2⟩ => by
    obtain ⟨m, hm, hy, hx⟩ := OrdAll.append h2
    refine ⟨m, by omega, hy, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨i, by omega, h1⟩
    · exact hx g hg

/-- **The order `rtPass` checks**: its groups' first labels at increasing
indices after the cells `pre` already passed. -/
theorem rtPass_ord : ∀ (s pre : List (Directive × Nat)) (seen : List Nat) (gs : List RGrp),
    (∀ c ∈ pre, ∀ m, c.1 = .label m → key m ∈ seen) → rtPass s seen gs = true →
    OrdAll (pre ++ s) pre.length gs
  | [], _, _, gs, _, h => by
    cases gs with
    | nil => trivial
    | cons _ _ => cases h
  | c :: cs, pre, seen, gs, hpre, h => by
    have ih := rtPass_ord cs (pre ++ [c])
    have happ : pre ++ [c] ++ cs = pre ++ c :: cs := by simp
    rw [← happ]
    change rtStep c cs (rtPass cs) seen gs = true at h
    unfold rtStep at h
    split at h
    next => trivial
    next g gs' =>
      split at h
      next m hcm =>
        have hpre' : ∀ c' ∈ pre ++ [c], ∀ m', c'.1 = .label m' → key m' ∈ key m :: seen := by
          intro c' hc' m' hm'
          rcases List.mem_append.mp hc' with hc' | hc'
          · exact List.mem_cons_of_mem _ (hpre c' hc' m' hm')
          · simp only [List.mem_singleton] at hc'; subst hc'
            rw [hcm, Directive.label.injEq] at hm'; simp [hm']
        cases hk : Nat.beq (key m) (key g.l)
        · rw [hk, Bool.cond_false] at h
          exact (ih _ _ hpre' h).mono (by simp)
        · rw [hk, Bool.cond_true] at h
          have hm : m = g.l := key_inj (Nat.beq_eq_true_eq _ _ ▸ hk)
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
          obtain ⟨⟨⟨hs, -⟩, -⟩, hr⟩ := h
          have hnm : ∀ c' ∈ pre, c'.1 ≠ .label m := fun c' hc' he => by
            have := memR_iff.mpr (hpre c' hc' m he); simp [this] at hs
          refine ⟨pre.length, Nat.le_refl _, ?_, ?_⟩
          · rw [← hm, happ, labelIdx_append_of _ hnm, labelIdx_head hcm]; simp
          · have := ih _ _ hpre' hr
            simpa using this
      next hnl =>
        refine (ih _ _ ?_ h).mono (by simp)
        intro c' hc' m' hm'
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hpre c' hc' m' hm'
        · simp only [List.mem_singleton] at hc'; subst hc'; exact absurd hm' (hnl m')

/-! ## Addresses -/

/-- The bytes of a list of cells. -/
def sz (xs : List (Directive × Nat)) : Nat := (xs.map (·.2)).sum

theorem sz_take_succ (cells : List (Directive × Nat)) (m : Nat) :
    sz (cells.take (m + 1)) = sz (cells.take m) + (cells[m]?.map (·.2)).getD 0 := by
  rw [List.take_add_one]; cases cells[m]? <;> simp [sz]

theorem sz_mono (cells : List (Directive × Nat)) {i j : Nat} (h : i ≤ j) :
    sz (cells.take i) ≤ sz (cells.take j) := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [sz_take_succ]; omega

/-- The bytes up to an index at most those of the whole list. -/
theorem sz_le (cells : List (Directive × Nat)) (j : Nat) : sz (cells.take j) ≤ sz cells := by
  have := sz_mono cells (Nat.le_max_left j cells.length)
  rwa [List.take_of_length_le (Nat.le_max_right j cells.length)] at this

/-- A label after a non-label cell of `z` bytes after the label at `i`: `z`
bytes more. -/
theorem sz_after {cells : List (Directive × Nat)} {i j : Nat} {l : Label} {c : Directive × Nat}
    (hj : labelIdx cells l = some j) (hc : cells[i + 1]? = some c) (hcl : c.1.isLabel = false) (hij : i < j) :
    sz (cells.take i) + c.2 ≤ sz (cells.take j) := by
  have hne : j ≠ i + 1 := fun e => by
    obtain ⟨z, hz⟩ := (labelIdx_spec hj).1; rw [e, hc] at hz; cases hz; simp [Directive.isLabel] at hcl
  have h1 := sz_mono cells (show i ≤ i + 1 by omega)
  have h2 := sz_take_succ cells (i + 1)
  rw [hc] at h2
  have h3 := sz_mono cells (show i + 1 + 1 ≤ j by omega)
  simp only [Option.map_some, Option.getD_some] at h2
  omega

/-- **`codeLabel` through `labelIdx`**: a label's address is the code base
plus the bytes before its first occurrence. -/
theorem codeLabel_eq : ∀ (cells : List (Directive × Nat)) (base : Nat) (l : String),
    codeLabel base cells l = (labelIdx cells l).map fun i => base + sz (cells.take i)
  | [], _, _ => rfl
  | c :: cs, base, l => by
    simp only [codeLabel, Scc.Sem.labelAddr, Scc.Cert.Rt.X64.labelIdx]
    by_cases hd : c.1 = .label l
    · simp [hd, Scc.Sem.X64.labelName, sz]
    · have h1 : Scc.Sem.X64.labelName c.1 ≠ some l := by
        obtain ⟨d, z⟩ := c; cases d <;> simp_all [Scc.Sem.X64.labelName]
      have ih := codeLabel_eq cs (base + c.2) l
      simp only [codeLabel] at ih
      simp only [h1, hd, ↓reduceIte, ih, Option.map_map]
      congr 1; funext i; simp [sz]; omega

/-- **A block's head cell** right after its label (at offset `0`). -/
theorem head_of_blockAtB {cells : List (Directive × Nat)} {l : Label} {c : Directive × Nat}
    {b : List (Directive × Nat)} (h : blockAtB cells l 0 (c :: b) = true) :
    ∃ i, labelIdx cells l = some i ∧ cells[i + 1]? = some c := by
  unfold blockAtB at h
  rw [after_eq] at h
  cases hi : labelIdx cells l with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, Option.map_some, Scc.Cert.Rt.X64.dropBytes] at h
    have h' := of_decide_eq_true h
    have hrc : (cellRun (cells.drop (i + 1)))[0]? = some c := by
      have := congrArg (·[0]?) h'
      simp only [List.getElem?_take] at this
      simpa using this
    have hcr := cellRun_append_runRest (cells.drop (i + 1))
    have hlt : 0 < (cellRun (cells.drop (i + 1))).length := by
      apply Classical.byContradiction; intro hc
      rw [List.eq_nil_of_length_eq_zero (l := cellRun (cells.drop (i + 1))) (by omega)] at hrc; simp at hrc
    refine ⟨i, rfl, ?_⟩
    have : cells[i + 1]? = (cellRun (cells.drop (i + 1)))[0]? := by
      rw [show i + 1 = i + 1 + 0 from rfl, ← List.getElem?_drop]
      conv => lhs; rw [← hcr]
      rw [List.getElem?_append_left hlt]
    rw [this, hrc]

/-- **A block's cell** `off` bytes into the run after its label. -/
theorem cell_of_blockAtB {cells : List (Directive × Nat)} {l : Label} {off : Nat} {c : Directive × Nat}
    {b : List (Directive × Nat)} (h : blockAtB cells l off (c :: b) = true) :
    ∃ i k, labelIdx cells l = some i ∧ sz (cells.take (i + 1 + k)) = sz (cells.take (i + 1)) + off ∧
      cells[i + 1 + k]? = some c := by
  unfold blockAtB at h
  rw [after_eq] at h
  cases hi : labelIdx cells l with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, Option.map_some] at h
    split at h
    next r hr =>
      have hrc : r[0]? = some c := by
        have h' := of_decide_eq_true h
        have := congrArg (·[0]?) h'
        simp only [List.getElem?_take] at this
        simpa using this
      obtain ⟨k, hk, hdr⟩ := dropBytes_sound _ _ hr
      have hcr := cellRun_append_runRest (cells.drop (i + 1))
      have hklt : k < (cellRun (cells.drop (i + 1))).length := by
        apply Classical.byContradiction; intro hc
        rw [List.drop_eq_nil_of_le (by omega)] at hdr; subst hdr; simp at hrc
      refine ⟨i, k, rfl, ?_, ?_⟩
      · have ht : (cells.drop (i + 1)).take k = (cellRun (cells.drop (i + 1))).take k := by
          conv => lhs; rw [← hcr]
          rw [List.take_append_of_le_length (by omega)]
        rw [List.take_add, sz, List.map_append, List.sum_append, ht, hk]; rfl
      · have : cells[i + 1 + k]? = (cellRun (cells.drop (i + 1)))[k]? := by
          rw [← List.getElem?_drop]
          conv => lhs; rw [← hcr]
          rw [List.getElem?_append_left hklt]
        rw [this, ← hrc, ← hdr, List.getElem?_drop]; rfl
    next => cases h

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
theorem phOf_eq {lo : Nat} {cells : List (Directive × Nat)} {a0 a1 : Nat} (hle : a0 ≤ a1)
    (hr : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, ∀ x y, r.resolve (codeLabel lo cells) = some (x, y) →
      y ≤ a0 ∨ a1 < x) :
    phOf lo cells a1 = phOf lo cells a0 := by
  have hr' : ∀ (rs : List PhRange) (rs' : List (Nat × Nat)), (∀ r ∈ rs, r ∈ bPR ++ bLR ++ bNR ++ bTR) →
      rs.mapM (PhRange.resolve (codeLabel lo cells)) = some rs' → inRs rs' a1 = inRs rs' a0 :=
    fun rs rs' hsub hm => inRs_eq hle fun p hp => by
      obtain ⟨r, hr0, e⟩ := mem_of_mapM hm p hp
      exact hr r (hsub r hr0) p.1 p.2 e
  unfold phOf phTabOf phTabBy
  cases hp : bPR.mapM (PhRange.resolve (codeLabel lo cells)) with
  | none => simp [bind]
  | some p =>
    cases hl : bLR.mapM (PhRange.resolve (codeLabel lo cells)) with
    | none => simp [bind]
    | some l =>
      cases hn : bNR.mapM (PhRange.resolve (codeLabel lo cells)) with
      | none => simp [bind]
      | some n =>
        cases ht : bTR.mapM (PhRange.resolve (codeLabel lo cells)) with
        | none => simp [bind]
        | some t =>
          simp only [bind, pure, Option.bind_some]
          simp only [Scc.Cert.Rt.X64.PhTab.ph]
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
    rw [← he.2, this, Nat.add_zero, Nat.mod_eq_of_lt hlt]; exact hle
  next => cases he

/-- A range starting at a label above `a1`, its offset in the address
space, starts above `a1`. -/
theorem resolve_after {code : String → Option Nat} {l1 l2 : String} {o1 o2 c a1 x y : Nat} (hc : code l1 = some c)
    (hlt : c + o1 < 2 ^ 64) (hlt1 : a1 < c) (he : PhRange.resolve code ⟨l1, o1, l2, o2⟩ = some (x, y)) :
    a1 < x := by
  unfold PhRange.resolve at he
  split at he
  next a b e1 _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    have : a = c := Option.some.inj (e1.symm.trans hc)
    rw [← he.1, this, Nat.mod_eq_of_lt hlt]; omega
  next => cases he

section Main

open Spike.Lib.X64.Rt (SetupCode rtCodeOkS rtCodeTabS startGrps mainSGrps tcbGrps tiGrpsAt takeGrps)
open Spike.Lib.X64.Rt.Code

/-- **The phase table at two pcs** `a0 ≤ a1`: `scc_rt_start`'s `.x0` and
`.x1` at or below `a0`, the labels of `scc_rt_alloc_tcb`,
`scc_rt_thread_init`, `scc_rt_stack_take` and its spin above `a1`. -/
theorem phOf_eq_of {lo : Nat} {cells : List (Directive × Nat)} {a0 a1 c0 c1 ct ci ck cs : Nat} (hle : a0 ≤ a1)
    (h0 : codeLabel lo cells Start.x0L = some c0) (h1 : codeLabel lo cells Start.x1L = some c1)
    (h0' : c0 ≤ a0) (h1' : c1 ≤ a0) (ha0 : a0 < 2 ^ 64)
    (ht : codeLabel lo cells Tcb.fnL = some ct) (hi : codeLabel lo cells Ti.fnL = some ci)
    (hk : codeLabel lo cells Take.fnL = some ck) (hs : codeLabel lo cells Take.spinL = some cs)
    (ht' : a1 < ct) (hi' : a1 < ci) (hk' : a1 < ck) (hs' : a1 < cs) (hct : ct < 2 ^ 64) (hci : ci < 2 ^ 64)
    (hck : ck < 2 ^ 64) (hcs : cs + 14 < 2 ^ 64) :
    phOf lo cells a1 = phOf lo cells a0 := by
  refine phOf_eq hle fun r hr x y he => ?_
  simp only [bPR, bLR, bNR, bTR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inl (resolve_before h0 (by omega) h0' he)
    | exact .inl (resolve_before h1 (by omega) h1' he)
    | exact .inr (resolve_after ht (by omega) ht' he)
    | exact .inr (resolve_after hi (by omega) hi' he)
    | exact .inr (resolve_after hk (by omega) hk' he)
    | exact .inr (resolve_after hs (by omega) hs' he)

/-- **`.x3`'s phase is `.x2`'s** in cells passing the runtime's code check
after a setup block at `sc` (`rtCodeOkS`), the code in the address space:
both resolve, `.x2` at or below `.x3`. -/
theorem ph_sp1_of_rtCodeOkS {lo : Nat} {cells : List (Directive × Nat)} {sc : SetupCode}
    (hc : rtCodeOkS cells sc = true) (hend : Scc.Sem.X64.codeEnd lo cells < 2 ^ 64) :
    ∃ a a1, codeLabel lo cells sc.sp0 = some a ∧ codeLabel lo cells sc.sp1 = some a1 ∧ a ≤ a1 ∧ a1 < 2 ^ 64 ∧
      phOf lo cells a1 = phOf lo cells a := by
  have hend' : lo + sz cells < 2 ^ 64 := hend
  have hord : OrdAll cells 0 (rtCodeTabS sc) := by
    simpa using rtPass_ord cells [] [] _ (by simp) hc
  have hall : RtAll cells (rtCodeTabS sc) := rtIn_sound hc
  simp only [rtCodeTabS, List.append_assoc] at hord hall
  obtain ⟨m0, -, hord, hst⟩ := OrdAll.append hord
  have hall2 := (Scc.Cert.Rt.X64.RtAll.append hall).2
  have hmain := (Scc.Cert.Rt.X64.RtAll.append hall2).1
  have htake := (Scc.Cert.Rt.X64.RtAll.append (Scc.Cert.Rt.X64.RtAll.append
    (Scc.Cert.Rt.X64.RtAll.append hall2).2).2).2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hsp1b, -⟩, -, -⟩ := hmain
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, hspb, -⟩, -, -⟩ := htake
  rw [mainSGrps, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append] at hord
  obtain ⟨i1, hi1, -, i2, hi2, -, i3, hi3, -, i4, hi4, hsp0i, i5, hi5, hsp1i, hrest⟩ := hord
  obtain ⟨i5', hsp1i', hx5⟩ := head_of_blockAtB hsp1b
  obtain ⟨js, ks, hjs, hks, hxs⟩ := cell_of_blockAtB hspb
  rw [hsp1i] at hsp1i'; cases hsp1i'
  have hcode : ∀ {l : Label} {j : Nat}, labelIdx cells l = some j →
      codeLabel lo cells l = some (lo + sz (cells.take j)) :=
    fun h => by rw [codeLabel_eq, h]; rfl
  -- the labels before
  obtain ⟨j0, hj0, hl0⟩ := hst ⟨Start.x0L, _, _⟩ (List.getElem_mem (l := startGrps) (n := 3) (by decide))
  obtain ⟨j1, hj1, hl1⟩ := hst ⟨Start.x1L, _, _⟩ (List.getElem_mem (l := startGrps) (n := 4) (by decide))
  -- the labels after
  have hmem : ∀ g ∈ tcbGrps ++ (tiGrpsAt sc.ti ++ takeGrps), ∃ j, i5 + 1 ≤ j ∧ labelIdx cells g.l = some j :=
    OrdAll.mem hrest
  obtain ⟨jt, hjt, hlt⟩ := hmem ⟨Tcb.fnL, _, _⟩ (List.mem_append_left _ (List.getElem_mem (l := tcbGrps) (n := 0)
    (by decide)))
  obtain ⟨ji, hji, hli⟩ := hmem ⟨Ti.fnL, _, _⟩ (List.mem_append_right _ (List.mem_append_left _
    (List.getElem_mem (l := tiGrpsAt sc.ti) (n := 0) (by simp [tiGrpsAt]))))
  obtain ⟨jk, hjk, hlk⟩ := hmem ⟨Take.fnL, _, _⟩ (List.mem_append_right _ (List.mem_append_right _
    (List.getElem_mem (l := takeGrps) (n := 0) (by decide))))
  obtain ⟨jsp, hjsp, hlsp⟩ := hmem ⟨Take.spinL, _, _⟩ (List.mem_append_right _ (List.mem_append_right _
    (List.getElem_mem (l := takeGrps) (n := 4) (by decide))))
  have hjj : jsp = js := Option.some.inj (hlsp.symm.trans hjs)
  subst hjj
  -- the bytes
  have e1 := sz_mono cells (show i4 ≤ i5 by omega)
  have e2 := sz_le cells i5
  have e3 := sz_mono cells (show j0 ≤ i4 by omega)
  have e4 := sz_mono cells (show j1 ≤ i4 by omega)
  have e5 : sz (cells.take i5) + 4 ≤ sz (cells.take jt) := sz_after hlt hx5 rfl (by omega)
  have e6 : sz (cells.take i5) + 4 ≤ sz (cells.take ji) := sz_after hli hx5 rfl (by omega)
  have e7 : sz (cells.take i5) + 4 ≤ sz (cells.take jk) := sz_after hlk hx5 rfl (by omega)
  have e8 : sz (cells.take i5) + 4 ≤ sz (cells.take jsp) := sz_after hlsp hx5 rfl (by omega)
  have e9 := sz_le cells jt
  have e10 := sz_le cells ji
  have e11 := sz_le cells jk
  have e12 := sz_le cells (jsp + 1 + ks)
  have e13 := sz_mono cells (show jsp ≤ jsp + 1 by omega)
  refine ⟨_, _, hcode hsp0i, hcode hsp1i, by omega, by omega, ?_⟩
  exact phOf_eq_of (by omega) (hcode hl0) (hcode hl1) (by omega) (by omega) (by omega) (hcode hlt) (hcode hli)
    (hcode hlk) (hcode hlsp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

end Main

section Rec

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rtCodeOkS)

/-- **`main`'s return address has the phase anchor's phase**
(`fnCode2Of`'s `RaOk` at `(setupMC sw).sp1`) at the record of an output
passing `placeOK` whose runtime's code holds at `setupMC sw` (A11,
`setupIn_of_placeOKAt`). -/
theorem raOk_main {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {sw : Nat} (hc : rtCodeOkS o.prog (setupMC sw) = true) :
    Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)
        (Int64.ofBitVec ((RuntimeLayout.ofPlaceOK h i).lab (setupMC sw).sp1).toBitVec).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)
        ((RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.LowerX64.raL).toBitVec.toNat := by
  obtain ⟨a, a1, ha, ha1, hle, hlt, hph⟩ := ph_sp1_of_rtCodeOkS hc (Spike.Lib.X64.PhRec.codeEnd_lt h i)
  have l0 := Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i _ _ ha
  have l1 := Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i _ _ ha1
  show phOf _ _ _ = phOf _ _ _
  rw [show Spike.Lib.LowerX64.raL = (setupMC sw).sp0 from rfl, l0, l1]
  have t1 : (Int64.ofNat a1).toBitVec.toNat = a1 := by simp [Nat.mod_eq_of_lt hlt]
  have t0 : (Int64.ofNat a).toBitVec.toNat = a := by simp [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]
  simp only [Int64.ofBitVec_toBitVec, t0, t1]
  exact hph

end Rec

/-- info: 'Spike.Lib.LowerX64.RaMain.OrdAll.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdAll.mono

/-- info: 'Spike.Lib.LowerX64.RaMain.OrdAll.mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdAll.mem

/-- info: 'Spike.Lib.LowerX64.RaMain.OrdAll.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdAll.append

/-- info: 'Spike.Lib.LowerX64.RaMain.rtPass_ord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rtPass_ord

/-- info: 'Spike.Lib.LowerX64.RaMain.sz_take_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms sz_take_succ

/-- info: 'Spike.Lib.LowerX64.RaMain.sz_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_mono

/-- info: 'Spike.Lib.LowerX64.RaMain.sz_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_le

/-- info: 'Spike.Lib.LowerX64.RaMain.sz_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sz_after

/-- info: 'Spike.Lib.LowerX64.RaMain.codeLabel_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms codeLabel_eq

/-- info: 'Spike.Lib.LowerX64.RaMain.head_of_blockAtB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms head_of_blockAtB

/-- info: 'Spike.Lib.LowerX64.RaMain.cell_of_blockAtB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cell_of_blockAtB

/-- info: 'Spike.Lib.LowerX64.RaMain.mem_of_mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_of_mapM

/-- info: 'Spike.Lib.LowerX64.RaMain.inRs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inRs_eq

/-- info: 'Spike.Lib.LowerX64.RaMain.phOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms phOf_eq

/-- info: 'Spike.Lib.LowerX64.RaMain.resolve_before' depends on axioms: [propext] -/
#guard_msgs in #print axioms resolve_before

/-- info: 'Spike.Lib.LowerX64.RaMain.resolve_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms resolve_after

/-- info: 'Spike.Lib.LowerX64.RaMain.phOf_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms phOf_eq_of

/-- info: 'Spike.Lib.LowerX64.RaMain.ph_sp1_of_rtCodeOkS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ph_sp1_of_rtCodeOkS

/-- info: 'Spike.Lib.LowerX64.RaMain.raOk_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms raOk_main

end Spike.Lib.LowerX64.RaMain
