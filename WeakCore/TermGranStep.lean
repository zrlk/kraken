import WeakCore.TermGranP
import WeakCore.TermB5

/-! # TermGranStep: `GranuleWP` across a thread step, at a fixed store typing and promise set

Operational half: a thread step keeps `GranuleWP sto · · P` (old `sto`, fixed `P`) when every write
target it names lies in a cell of `sto` whose one-word units start no two-word unit and whose
two-word units start two-word units (`WT`), and the next fresh label is untyped and carries no pair
store. -/

namespace TermGranStep
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermGranW TermGranP
open TermCert TermB5
open TermFul (loadUnits_keep projM_keep)
open WeakMem (Msg Memory Address Ts Arch AllocLabel)

/-- A write target of units `us` from `b`, in `sto`: its one-word units neither start nor end a
two-word unit of the cell, its two-word units start two-word units of it. -/
def WT (sto : Sto) (b : Address) (us : List Acc) : Prop :=
  ∃ cl, sto b.label = some cl ∧ (∀ j, TermStep.OneAt us j → ¬ TwoAtT cl.ty (b.offset + j)) ∧
    (∀ j, TwoAt us j → TwoAtT cl.ty (b.offset + j)) ∧
    (∀ j, TermStep.OneAt us j → ∀ o, b.offset + j = o + 1 → ¬ TwoAtT cl.ty o)

/-- The next fresh label: untyped in `sto`, no pair store there. -/
def FreshOK (g : G) (sto : Sto) (mem : Memory) (pairs : List Ts) (n : Nat) : Prop :=
  sto (freshLabel g.lbase g.n g.i n) = none ∧ NoPairAt mem pairs (freshLabel g.lbase g.n g.i n)

theorem gran_load {sto : Sto} {P : List Ts} {s s' : St}
    (h : s'.mem = s.mem ∧ s'.pairs = s.pairs ∧ s'.promises = s.promises)
    (hG : GranuleWP sto s.mem s.pairs P) : GranuleWP sto s'.mem s'.pairs P := by
  rw [h.1, h.2.1]; exact hG

theorem units_gran {k : Promises.Knobs} {arch : Arch} {pw : Word} {b : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {sto : Sto} {P : List Ts} {s s1 s' : St}
    (hk : s1.mem = s.mem ∧ s1.pairs = s.pairs ∧ s1.promises = s.promises)
    (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1) (hW : WT sto b us)
    (hG : GranuleWP sto s.mem s.pairs P) : GranuleWP sto s'.mem s'.pairs P := by
  obtain ⟨cl, hc, h1, h2, h3⟩ := hW
  refine granuleWP_storeUnits hc us ws 0 s1 s' hs (fun j hj => ?_) (fun j hj o ho => ?_) (fun j hj => ?_)
    (gran_load hk hG)
  · rw [Nat.add_zero]; exact h1 j hj
  · exact h3 j hj o (by rw [Nat.add_zero] at ho; exact ho)
  · rw [Nat.add_zero]; exact h2 j hj

theorem units_gran0 {k : Promises.Knobs} {arch : Arch} {pw : Word} {b : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {sto : Sto} {P : List Ts} {s s' : St}
    (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s) (hW : WT sto b us)
    (hG : GranuleWP sto s.mem s.pairs P) : GranuleWP sto s'.mem s'.pairs P :=
  units_gran ⟨rfl, rfl, rfl⟩ hs hW hG

/-- No pair store starts at a one-word target. -/
theorem noPair_of_wt1 {sto : Sto} {mem : Memory} {pairs P : List Ts} {b : Address}
    (hW : WT sto b [.one]) (hG : GranuleWP sto mem pairs P) :
    ∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc ≠ b := by
  intro q hq m0 h0 e
  obtain ⟨cl, hc, h1, -⟩ := hW
  have := hG.2.2.1 q hq m0 cl h0 (by rw [e]; exact hc)
  rw [e] at this
  exact h1 0 ⟨0, rfl, rfl⟩ (by rw [Nat.add_zero]; exact this)

/-- No pair store starts at the second word of a two-word target. -/
theorem noPair_of_wt2 {sto : Sto} {mem : Memory} {pairs P : List Ts} {b : Address}
    (hW : WT sto b [.two]) (hG : GranuleWP sto mem pairs P) :
    ∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc ≠ b.next := by
  intro q hq m0 h0 e
  obtain ⟨cl, hc, -, h2, -⟩ := hW
  have := hG.2.2.1 q hq m0 cl h0 (by rw [e]; exact hc)
  rw [e] at this
  have h20 := h2 0 TermB5.twoAt_two0
  rw [Nat.add_zero] at h20
  exact TwoAtT_not_succ h20 this

theorem rmw_gran {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {x : Memory × Promises.Thread}
    {sto : Sto} {P : List Ts}
    (h : x ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hW : WT sto a [.one]) (hG : GranuleWP sto mem pairs P) : GranuleWP sto x.1 pairs P :=
  granuleWP_stepRmw (th' := x.2) h hG (noPair_of_wt1 hW hG) fun cl o hc ho => by
    obtain ⟨cl', hc', -, -, h3⟩ := hW
    rw [hc] at hc'; cases hc'
    exact h3 0 ⟨0, rfl, rfl⟩ o (by rw [Nat.add_zero]; exact ho)

theorem rmwPair_gran {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    {x : Memory × List Ts × Promises.Thread} {sto : Sto} {P : List Ts}
    (h : x ∈ Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hW : WT sto a [.two]) (hG : GranuleWP sto mem pairs P) : GranuleWP sto x.1 x.2.1 P := by
  refine granuleWP_stepRmwPair (th' := x.2.2) h hG (noPair_of_wt2 hW hG) (fun cl hc => ?_)
  obtain ⟨cl', hc', -, h2, -⟩ := hW
  rw [hc] at hc'; cases hc'
  have := h2 0 TermB5.twoAt_two0
  rw [Nat.add_zero] at this; exact this

theorem alloc_nallocE {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) :
    r.1.nalloc = s.nalloc + 1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  have := TermTyped.storeUnits_nallocT _ _ _ _ s' hs
  exact this

theorem alloc_gran {k : Promises.Knobs} {arch : Arch} {g : G} {us : List Acc} {ws : List Word} {s : St}
    {r : St × Word} {sto : Sto} {P : List Ts}
    (hr : r ∈ alloc k arch (freshLabel g.lbase g.n g.i s.nalloc) us ws s)
    (hF : FreshOK g sto s.mem s.pairs s.nalloc) (hG : GranuleWP sto s.mem s.pairs P) :
    GranuleWP sto r.1.mem r.1.pairs P :=
  granuleWP_alloc hr hG hF.2 hF.1

theorem injM_gran {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    {sto : Sto} {P : List Ts} (h : r ∈ injM g s ty j p)
    (hF : s.nalloc < r.1.nalloc → FreshOK g sto s.mem s.pairs s.nalloc) (hG : GranuleWP sto s.mem s.pairs P) :
    GranuleWP sto r.1.mem r.1.pairs P := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have hn := alloc_nallocE hs
      have := alloc_gran hs (hF (by
        dsimp only at hn ⊢
        split
        · show s.nalloc < s'.nalloc; omega
        · show s.nalloc < s'.nalloc; omega)) hG
      dsimp only
      split
      · exact this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact hG

theorem projInj_gran {g : G} {s : St} {t S : Ty} {ws : List Word} {j : Nat} {p : List Word}
    {x : St × Nat × List Word} {y : St × List Word} {sto : Sto} {P : List Ts}
    (hx : x ∈ projM g s t ws) (hy : y ∈ injM g x.1 S j p)
    (hF : s.nalloc < y.1.nalloc → FreshOK g sto s.mem s.pairs s.nalloc) (hG : GranuleWP sto s.mem s.pairs P) :
    GranuleWP sto y.1.mem y.1.pairs P := by
  obtain ⟨e1, e2, -⟩ := projM_keep hx
  have e4 := TermStepper.projM_nalloc hx
  refine injM_gran hy (fun hlt => ?_) ?_
  · rw [e1, e2, e4]; exact hF (by rw [← e4]; exact hlt)
  · rw [e1, e2]; exact hG

theorem allocBuf_gran {g : G} {n : Nat} {z : Option (List WeakMem.Val)} {s : St} {sto : Sto} {P : List Ts}
    (hF : s.nalloc < (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n z s).1.nalloc →
      FreshOK g sto s.mem s.pairs s.nalloc) (hG : GranuleWP sto s.mem s.pairs P) :
    GranuleWP sto (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n z s).1.mem
      (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n z s).1.pairs P :=
  granuleWP_allocBuf hG (hF (by rw [(allocBuf_grows _ _ _ s).2.2]; omega)).2
    (hF (by rw [(allocBuf_grows _ _ _ s).2.2]; omega)).1

/-- **An operation** keeps `GranuleWP` at `sto`, `P`. -/
theorem evalOp_gran {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    {sto : Sto} {P : List Ts} (h : r ∈ evalOp g env σs s op)
    (hW : ∀ b us, OpNewR g env s op b us → WT sto b us)
    (hF : s.nalloc < r.1.nalloc → FreshOK g sto s.mem s.pairs s.nalloc) (hG : GranuleWP sto s.mem s.pairs P) :
    GranuleWP sto r.1.mem r.1.pairs P := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact hG | exact allocBuf_gran hF hG)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact gran_load (loadUnits_keep _ _ _ _ hx) hG
         | exact units_gran0 hx (hW _ _ (.inl ⟨_, _, _, by dsimp only [TermFul.UnitsOp]; fillx⟩)) hG
         | exact units_gran0 hx (hW _ _ (.inr (.inl ⟨_, _, _, _, _, _, _, rfl, ‹_›, ‹_›, rfl⟩))) hG
         | exact alloc_gran hx (hF (by rw [alloc_nallocE hx]; omega)) hG
         | exact rmw_gran hx (hW _ _ (.inr (.inr ⟨_, _, _, _, _, _, _, rfl, ‹_›, ‹_›, rfl⟩))) hG
         | exact hG)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact projInj_gran hx hy hF hG
         | exact units_gran (loadUnits_keep _ _ _ _ hx) hy
             (hW _ _ (.inl ⟨_, _, _, by dsimp only [TermFul.UnitsOp]; fillx⟩)) hG)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact units_gran (loadUnits_keep _ _ _ _ hx) hy
           (hW _ _ (.inl ⟨_, _, _, by dsimp only [TermFul.UnitsOp]; fillx⟩)) hG
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact gran_load (loadUnits_keep _ _ _ _ hx) hG)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_gran hF hG)

/-- **A thread step** keeps `GranuleWP` at `sto`, `P`. -/
theorem tstep_gran {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {sto : Sto} {P : List Ts} (h : r ∈ tstep g mem pairs th)
    (hW : ∀ x op e b us, th.term = .let_ x op e → OpNewR g th.env (stOf mem pairs th) op b us → WT sto b us)
    (hC : ∀ acq rel w e v tn ok fail tw pw b, th.term = .cas acq rel w e v tn ok fail →
      evalAt th.env w = some (tw, [pw]) → addrOf pw = some b → WT sto b [.one])
    (hCP : ∀ acq rel w e0 e1 v0 v1 tn ok fail tw pw b, th.term = .casp acq rel w e0 e1 v0 v1 tn ok fail →
      evalAt th.env w = some (tw, [pw]) → addrOf pw = some b → WT sto b [.two])
    (hF : th.nalloc < r.2.2.nalloc → FreshOK g sto mem pairs th.nalloc) (hG : GranuleWP sto mem pairs P) :
    GranuleWP sto r.1 r.2.1 P := by
  simp only [tstep] at h
  split at h <;> rename_i hT
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact hG)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact hG)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact hG)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_gran hx (fun b us => hW _ _ _ b us hT) hF hG
         | exact rmw_gran hx (hC _ _ _ _ _ _ _ _ _ _ _ hT ‹_› ‹_›) hG
         | exact rmwPair_gran hx (hCP _ _ _ _ _ _ _ _ _ _ _ _ _ hT ‹_› ‹_›) hG)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact projInj_gran hx hy hF hG)
    | (simp only [List.mem_map] at h  -- new arm: record write
       obtain ⟨x, hx, rfl⟩ := h
       try dsimp only
       revert hF
       split
       all_goals
         intro hF
         first
           | exact evalOp_gran hx (fun b us => hW _ _ _ b us hT) hF hG
           | exact rmw_gran hx (hC _ _ _ _ _ _ _ _ _ _ _ hT ‹_› ‹_›) hG
           | exact rmwPair_gran hx (hCP _ _ _ _ _ _ _ _ _ _ _ _ _ hT ‹_› ‹_›) hG)

/-! ## Typed targets -/

theorem wt_of_ua {η : TEnv} {sto : Sto} {b : Address} {us : List Acc}
    (h1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, η.sto l = some c → LayT c.ty)
    (h : TermTyped.UnitsAt η b us) : WT sto b us := by
  obtain ⟨c, U, hsto, hat, hus⟩ := h
  exact ⟨c, h1 _ _ hsto, fun j hj => notTwoAtT_of_oneAt hat hus (TermStepper.oneAt_ful hj),
    fun j hj => twoAtT_of_atOff (hLay _ _ hsto) hat hus hj,
    fun j hj o ho hT => (TermPlantF.oneAt_twoAtT hat hus (TermStepper.oneAt_ful hj) hT).2 ho⟩

theorem wt_of_sw {η : TEnv} {sto : Sto} {loc : Address}
    (h1 : ∀ l c, η.sto l = some c → sto l = some c) (h : TermTyped.SWAt η loc) : WT sto loc [.one] := by
  obtain ⟨cl, o, U, us, j, hsto, hat, hus, hj, ho⟩ := h
  refine ⟨cl, h1 _ _ hsto, fun j' hj' => ?_, fun j' hj' => ?_, fun j' hj' o2 ho2 hT => ?_⟩
  · obtain ⟨i, hi, e⟩ := hj'
    cases i with
    | zero =>
      simp at e; subst e
      show ¬TwoAtT cl.ty (loc.offset + 0)
      rw [Nat.add_zero, ho]; exact notTwoAtT_of_oneAt hat hus hj
    | succ i => simp at hi
  · obtain ⟨i, hi, -⟩ := hj'
    cases i with
    | zero => simp at hi
    | succ i => simp at hi
  · obtain ⟨i, hi, e⟩ := hj'
    cases i with
    | zero =>
      simp at e; subst e
      exact (TermPlantF.oneAt_twoAtT hat hus hj hT).2 (by simp only [nWords, List.map_nil, List.sum_nil, Nat.add_zero] at ho2; rw [← ho, ho2])
    | succ i => simp at hi

/-- **Typed core**: a typed, in-scope thread's step keeps `GranuleWP` at the old `sto` and a fixed
`P`, given `E.sto ⊆ sto`, laid-out cells in `E`, and the next fresh label untyped and pair-free. -/
theorem tstep_granT {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {E : TEnv} {sto : Sto} {P : List Ts} (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th))
    (hsc : TermTyped.ScopeOK p th) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (hLay : ∀ l c, E.sto l = some c → LayT c.ty)
    (hF : th.nalloc < r.2.2.nalloc → FreshOK g sto mem pairs th.nalloc)
    (hr : r ∈ tstep g mem pairs th) (hG : GranuleWP sto mem pairs P) : GranuleWP sto r.1 r.2.1 P := by
  obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩ := hI
  have hD := hsc ρ η cx hE hT htv hi
  refine tstep_gran hr ?_ ?_ ?_ hF hG
  · intro x op e b us hterm hn
    rw [hterm] at hT hD
    cases hT with
    | let_ hop _ =>
        rcases hD with hs | ⟨-, hc⟩
        · rcases hn with ⟨pw, rel, ws, hu⟩ | ⟨rel, a, v0, v1, tk, t', pw, rfl, hea, hb, rfl⟩ |
              ⟨o, acq, rel, a, v, t', pw, rfl, hea, hb, rfl⟩
          · exact wt_of_ua (η := η) h1 hLay (TermTyped.unitsOp_ua hop hs hi hE htv hu)
          · exact wt_of_ua (η := η) h1 hLay (TermStepper.stp_ua hop hs hi hea hb)
          · exact wt_of_sw (η := η) h1 (TermTyped.fetch_sw hop hs hi hE htv hM hea hb)
        · obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := hc <;> cases he <;>
            rcases hn with ⟨_, _, _, hu⟩ | ⟨_, _, _, _, _, _, _, he2, -⟩ | ⟨_, _, _, _, _, _, _, he2, -⟩ <;>
            first | (simp [TermFul.UnitsOp] at hu) | (cases he2)
  · intro acq rel w e v tn ok fail tw pw b hterm hea hb
    rw [hterm] at hT hD
    rcases hD with hs | ⟨-, hc⟩
    · exact wt_of_sw (η := η) h1 (TermTyped.cas_sw hT hs hi hE htv hM hea hb)
    · obtain ⟨_, _, ⟨_, _, he⟩ | ⟨_, he⟩ | ⟨_, he⟩⟩ := hc <;> cases he
  · intro acq rel w e0 e1 v0 v1 tn ok fail tw pw b hterm hea hb
    rw [hterm] at hT hD
    rcases hD with hs | ⟨-, hc⟩
    · exact wt_of_ua (η := η) h1 hLay (TermStepper.casp_ua hT hs hi hea hb)
    · obtain ⟨_, _, ⟨_, _, he⟩ | ⟨_, he⟩ | ⟨_, he⟩⟩ := hc <;> cases he

/-! ## Fulfilments, the new store typing, and the headline forms -/

/-- `SWOne_holds`' body, without its (unused) `PromAbove` argument. -/
theorem sw_at {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {loc : Address} {val : WeakMem.Val} (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hsw : TermFul.SW g mem pairs th loc val) : TermTyped.SWAt η loc := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, rfl, -⟩ |
            ⟨o, acq, rel, a, v, t, t', pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · exact TermTyped.unitsOp_sw hop hsc hi hE htv hu hj
        · exact TermTyped.fetch_sw hop hsc hi hE htv hm hea hb
  · rw [hterm] at hT hsc
    exact TermTyped.cas_sw hT hsc hi hE htv hm hea hb

/-- **The new store typing**: a cell new to `sto'` has every pair store at its label starting a
two-word unit of it (`hNC`), and every non-`P` message at a second word of a two-word unit of it
holding no pointer or ending a pair store (`hNC4`). -/
theorem granuleWP_toSto {sto sto' : Sto} {mem : Memory} {pairs P : List Ts}
    (h3 : ∀ l c, sto l = some c → sto' l = some c) (hP : GranuleWP sto mem pairs P)
    (hNC : ∀ q ∈ pairs, ∀ (m0 : Msg) (cl : Cell), mem[q]? = some m0 → sto' m0.loc.label = some cl →
      sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset)
    (hNC4 : ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), mem[v]? = some mv → v ∉ P →
      sto' mv.loc.label = some cl → sto mv.loc.label = none → mv.loc.offset = o + 1 → TwoAtT cl.ty o →
      (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1) : GranuleWP sto' mem pairs P := by
  refine granuleWP_lift hP fun l c hc' => ?_
  cases hs : sto l with
  | none =>
      refine .inr ⟨fun q hq m0 h0 hl => by subst hl; exact hNC q hq m0 c h0 hc' hs,
        fun v mv o hv hPv hl ho hT => ?_⟩
      subst hl; exact hNC4 v mv c o hv hPv hc' hs ho hT
  | some c0 =>
      have := h3 _ _ hs
      rw [hc'] at this; cases this
      exact .inl rfl

/-- The next fresh label of a step that allocates: untyped (`hfr`), no pair store (`FreshLP`,
`PromOK`). -/
theorem freshOK_of {g : G} {E : TEnv} {sto : Sto} {mem : Memory} {pairs : List Ts} {th : TTh} {n' : Nat}
    (hM : MemInv g E (stOf mem pairs th)) (hfr : ∀ l, FreshIn g th.nalloc n' l → sto l = none) :
    th.nalloc < n' → FreshOK g sto mem pairs th.nalloc := fun hlt =>
  ⟨hfr _ ⟨th.nalloc, Nat.le_refl _, hlt, rfl⟩, fun q hq m0 h0 hl =>
    hM.2.2.2.2.2.2.2.2.2.2.2.1 q ((hM.2.2.2.1.1 th.nalloc (Nat.le_refl _)).2.1 q m0 h0 hl) hq⟩

/-- **G2** (`GranuleWP` across a typed thread step, to the new store typing and promise set). -/
theorem granuleWP_step {p : Prog} {g : G} {E : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {r : Memory × List Ts × TTh}
    (h1 : ∀ l c, E.sto l = some c → sto l = some c) (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th)) (hr : r ∈ tstep g mem pairs th)
    (hsc : TermTyped.ScopeOK p th) (hG : GranuleWP sto mem pairs th.promises)
    (hfr : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → sto l = none)
    (hLay : ∀ l c, E.sto l = some c → LayT c.ty)
    (hNC : ∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → sto' m0.loc.label = some cl →
      sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset)
    (hNC4 : ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
      sto' mv.loc.label = some cl → sto mv.loc.label = none → mv.loc.offset = o + 1 → TwoAtT cl.ty o →
      (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1) :
    GranuleWP sto' r.1 r.2.1 r.2.2.promises := by
  have hPO := hM.2.2.2.2.2.2.2.2.2.2
  have hc := tstep_granT hI hM hsc h1 hLay (freshOK_of hM hfr) hr hG
  obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩ := hI
  have hD := hsc ρ η cx hE hT htv hi
  obtain ⟨-, hrem⟩ := TermFul.tstep_fulfil (MemInv_promLt hM) hPO.2.1 hr
  have hext := (TermFul.tstep_grow hr).1
  have hWv : ∀ v, v ∈ th.promises → v ∉ r.2.2.promises → ∃ m, r.1[v]? = some m ∧ WT sto m.loc [.one] := by
    intro v hv hv2
    obtain ⟨m, hm, hsw, -⟩ := hrem v hv hv2
    exact ⟨m, hext v m hm, wt_of_sw (η := η) h1 (sw_at hE hT htv hi hM (TermTyped.scopeD_SW hD hsw) hsw)⟩
  refine granuleWP_toSto h3 (granuleWP_setP hc (fun v hv hv2 q hq m0 mv h0 hmv _ e => ?_)
    (fun v hv hv2 mv cl o hmv hcl ho hTo => ?_)) hNC hNC4
  · obtain ⟨m, hm, hW⟩ := hWv v hv hv2
    rw [hm] at hmv; cases hmv
    exact noPair_of_wt1 hW hc q hq m0 h0 e.symm
  · obtain ⟨m, hm, cl', hc', -, -, h4⟩ := hWv v hv hv2
    rw [hm] at hmv; cases hmv
    rw [hcl] at hc'; cases hc'
    exact absurd hTo (h4 0 ⟨0, rfl, rfl⟩ o (by rw [Nat.add_zero]; exact ho))

/-- **G1** (`GranuleW`, i.e. `P = []` before and after; `hNC4` at every message). -/
theorem granuleW_step {p : Prog} {g : G} {E : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {r : Memory × List Ts × TTh}
    (h1 : ∀ l c, E.sto l = some c → sto l = some c) (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th)) (hr : r ∈ tstep g mem pairs th)
    (hsc : TermTyped.ScopeOK p th) (hG : GranuleW sto mem pairs)
    (hfr : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → sto l = none)
    (hLay : ∀ l c, E.sto l = some c → LayT c.ty)
    (hNC : ∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → sto' m0.loc.label = some cl →
      sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset)
    (hNC4 : ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv →
      sto' mv.loc.label = some cl → sto mv.loc.label = none → mv.loc.offset = o + 1 → TwoAtT cl.ty o →
      (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1) :
    GranuleW sto' r.1 r.2.1 :=
  granuleW_of_nil (granuleWP_toSto h3 (tstep_granT hI hM hsc h1 hLay (freshOK_of hM hfr) hr
    (granuleWP_of [] hG)) hNC fun v mv cl o hv _ => hNC4 v mv cl o hv)

/-- **G1, `FootNCE` form**: `granuleW_step` with `hNC4` only off the result's promises (the
`FootNCE` form), the promises' case closed by `hNF` (no outstanding promise lies at a label new to
`sto'`, `PtrRtsThreadGL`'s `hNF`). -/
theorem granuleW_stepNF {p : Prog} {g : G} {E : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {r : Memory × List Ts × TTh}
    (h1 : ∀ l c, E.sto l = some c → sto l = some c) (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th)) (hr : r ∈ tstep g mem pairs th)
    (hsc : TermTyped.ScopeOK p th) (hG : GranuleW sto mem pairs)
    (hfr : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → sto l = none)
    (hLay : ∀ l c, E.sto l = some c → LayT c.ty)
    (hNF : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m → sto m.loc.label = none → sto' m.loc.label = none)
    (hNC : ∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → sto' m0.loc.label = some cl →
      sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset)
    (hNC4 : ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
      sto' mv.loc.label = some cl → sto mv.loc.label = none → mv.loc.offset = o + 1 → TwoAtT cl.ty o →
      (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1) :
    GranuleW sto' r.1 r.2.1 :=
  granuleW_step h1 h3 hI hM hr hsc hG hfr hLay hNC fun v mv cl o hv hcl hn ho hT => by
    by_cases hp : v ∈ r.2.2.promises
    · rw [hNF v hp mv hv hn] at hcl; cases hcl
    · exact hNC4 v mv cl o hv hp hcl hn ho hT

end TermGranStep

#print axioms TermGranStep.evalOp_gran
#print axioms TermGranStep.tstep_gran
#print axioms TermGranStep.tstep_granT
#print axioms TermGranStep.granuleW_stepNF
#print axioms TermGranStep.sw_at
#print axioms TermGranStep.granuleWP_toSto
#print axioms TermGranStep.freshOK_of
#print axioms TermGranStep.granuleWP_step
#print axioms TermGranStep.granuleW_step
