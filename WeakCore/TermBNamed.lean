import WeakCore.TermPlantF

/-!
# TermBNamed: box payloads stay named across a thread step (`bnamedT`, T18)

* §1 `WrV L s s'`: every message of `s'` that is not a promise is an old non-promise message
  of `s`, or holds a value naming only labels in `L` (`NV L`).  Proved per machine primitive and
  lifted to `evalOp`/`tstep` under hypotheses on the step's written operands (`OpWOK`).
-/

namespace TermBNamed
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermTyped TermCert
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Written values -/

/-- A value names only labels in `L`. -/
def NV (L : AllocLabel → Prop) (v : WeakMem.Val) : Prop := ∀ (a : Address) (g : Nat), v = .loc a g → L a.label

/-- Every word names only labels in `L`. -/
def AllNV (L : AllocLabel → Prop) (ws : List Word) : Prop := ∀ w ∈ ws, NV L w.val

theorem nv_num (L : AllocLabel → Prop) (n : Nat) : NV L (.num n) := fun _ _ h => nomatch h
theorem nv_undef (L : AllocLabel → Prop) : NV L .undef := fun _ _ h => nomatch h
theorem nv_null (L : AllocLabel → Prop) : NV L .null := fun _ _ h => nomatch h

theorem allNV_nil (L : AllocLabel → Prop) : AllNV L [] := fun _ h => by cases h

theorem allNV_cons {L : AllocLabel → Prop} {w : Word} {ws : List Word} (h1 : NV L w.val) (h2 : AllNV L ws) :
    AllNV L (w :: ws) := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact h1
  · exact h2 x hx

theorem allNV_append {L : AllocLabel → Prop} {ws us : List Word} (h1 : AllNV L ws) (h2 : AllNV L us) :
    AllNV L (ws ++ us) := by
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

theorem allNV_head {L : AllocLabel → Prop} {w : Word} {ws : List Word} (h : AllNV L (w :: ws)) : NV L w.val :=
  h w (List.mem_cons_self ..)

theorem allNV_tail {L : AllocLabel → Prop} {w : Word} {ws : List Word} (h : AllNV L (w :: ws)) : AllNV L ws :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- Every non-promise message of `mem'` (promises `P'`) is an old non-promise message, or holds
a value naming only `L`. -/
def WrVM (L : AllocLabel → Prop) (mem : Memory) (P : List Ts) (mem' : Memory) (P' : List Ts) : Prop :=
  ∀ (t : Ts) (m : Msg), mem'[t]? = some m → t ∉ P' → (mem[t]? = some m ∧ t ∉ P) ∨ NV L m.val

/-- `WrVM` on states. -/
def WrV (L : AllocLabel → Prop) (s s' : St) : Prop := WrVM L s.mem s.promises s'.mem s'.promises

theorem WrVM.refl (L : AllocLabel → Prop) (mem : Memory) (P : List Ts) : WrVM L mem P mem P :=
  fun _ _ h hp => Or.inl ⟨h, hp⟩

theorem WrVM.trans {L : AllocLabel → Prop} {m1 m2 m3 : Memory} {P1 P2 P3 : List Ts}
    (a : WrVM L m1 P1 m2 P2) (b : WrVM L m2 P2 m3 P3) : WrVM L m1 P1 m3 P3 := by
  intro t m h hp
  rcases b t m h hp with ⟨h2, hp2⟩ | hv
  · exact a t m h2 hp2
  · exact Or.inr hv

theorem WrV.refl (L : AllocLabel → Prop) (s : St) : WrV L s s := WrVM.refl L _ _

theorem WrV.trans {L : AllocLabel → Prop} {s1 s2 s3 : St} (a : WrV L s1 s2) (b : WrV L s2 s3) : WrV L s1 s3 :=
  WrVM.trans a b

theorem WrVM.push {L : AllocLabel → Prop} {mem : Memory} {P : List Ts} (m0 : Msg) (hv : NV L m0.val) :
    WrVM L mem P (mem.push m0) P := by
  intro t m h hp
  rw [Array.getElem?_push] at h
  by_cases e : t = mem.size
  · simp only [e, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact Or.inr hv
  · simp only [e, ↓reduceIte] at h
    exact Or.inl ⟨h, hp⟩

theorem WrVM.fulfil {L : AllocLabel → Prop} {mem : Memory} {P : List Ts} {t0 : Ts} {pm : Msg}
    (h0 : mem[t0]? = some pm) (hv : NV L pm.val) : WrVM L mem P mem (P.erase t0) := by
  intro t m h hp
  by_cases e : t = t0
  · subst e
    rw [h0] at h
    cases h
    exact Or.inr hv
  · exact Or.inl ⟨h, fun h' => hp ((List.mem_erase_of_ne e).2 h')⟩

theorem WrVM.fold {L : AllocLabel → Prop} {mem : Memory} {P : List Ts} (n : Nat) (f : Nat → Msg)
    (hf : ∀ j, NV L (f j).val) : WrVM L mem P ((List.range n).foldl (fun m j => m.push (f j)) mem) P := by
  induction n with
  | zero => exact WrVM.refl _ _ _
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      exact WrVM.trans ih (WrVM.push _ (hf n))

/-- The value a store of `dataE r w` writes from a register file holding `w` at `r`. -/
theorem dataE_val (s : St) (pw w : Word) :
    (match dataE 1 w with
      | .const c => c
      | .reg r => ((mth s pw w w).regs r).val) = w.val := by
  cases h : w.val <;> simp [dataE, h, mth, regsOf]

theorem stepStore_wrV {L : AllocLabel → Prop} {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel)
    (hc : ∀ c, e = .const c → NV L c) (hr : ∀ r, e = .reg r → NV L (th.regs r).val) :
    WrVM L mem th.promises mem' th'.promises := by
  cases e <;>
  · first | have hv := hc _ rfl | have hv := hr _ rfl
    simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact WrVM.push _ hv
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            exact WrVM.fulfil hm (by rw [hc.1.1.2]; exact hv)
          · simp at hf

theorem stepStore_mth {L : AllocLabel → Prop} {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {s : St} {pw w : Word} {th' : Promises.Thread} {a : Address} {deps : List WeakMem.Reg}
    {rel : Bool} (h : (mem', th') ∈ Promises.stepStore k arch mem (mth s pw w w) a (dataE 1 w) deps rel)
    (hw : NV L w.val) : WrVM L mem s.promises mem' th'.promises :=
  stepStore_wrV h (fun c e => by
      unfold dataE at e; split at e
      · cases e
      · cases e; assumption)
    (fun r e => by
      unfold dataE at e; split at e
      · cases e
        rename_i a g hh
        have e1 : ((mth s pw w w).regs 1) = w := by simp [mth, regsOf]
        rw [e1]; exact hw
      · cases e)

theorem nv_apply {L : AllocLabel → Prop} (kind : WeakMem.RmwKind) (x : WeakMem.Val) {y : WeakMem.Val}
    (hy : NV L y) : NV L (kind.apply x y) := by
  cases kind <;> cases x <;> cases y <;> first | exact hy | exact nv_num _ _ | exact nv_undef _

theorem lock_promises {arch' : Arch} (x : Promises.Thread) :
    (if arch' = .tso then Promises.stepFence x .sy else x).promises = x.promises := by
  split
  · rfl
  · rfl

theorem stepRmw_wrV_at {L : AllocLabel → Prop} {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {pairs : List Ts} {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hv : ∀ x, NV L (kind.apply x (Promises.rmwNewVal th.regs newv))) :
    WrVM L mem th.promises mem' th'.promises := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [lock_promises]
    exact WrVM.refl _ _ _
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [lock_promises]
        exact WrVM.push _ (hv _)
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hc, rfl, rfl⟩ := hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rw [lock_promises]
          exact WrVM.fulfil hm (by rw [hc.1.1.1.2]; exact hv _)

theorem stepRmw_wrV {L : AllocLabel → Prop} {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {pairs : List Ts} {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hv : ∀ x, NV L (kind.apply x (Promises.rmwNewVal th.regs newv))) :
    WrVM L mem th.promises mem' th'.promises := by
  have hx := stepRmw_wrV_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (fun x => by rw [lockTh_regs]; exact hv x)
  rwa [lockTh_prom] at hx

theorem rmwNewVal_dataE1 (s : St) (pw w0 w1 : Word) :
    Promises.rmwNewVal (mth s pw w0 w1).regs (dataE 1 w0) = w0.val := by
  cases h : w0.val <;> simp [dataE, h, Promises.rmwNewVal, mth, regsOf]

theorem rmwNewVal_dataE2 (s : St) (pw w0 w1 : Word) :
    Promises.rmwNewVal (mth s pw w0 w1).regs (dataE 2 w1) = w1.val := by
  cases h : w1.val <;> simp [dataE, h, Promises.rmwNewVal, mth, regsOf]

theorem stepStorePair_mth {L : AllocLabel → Prop} (mem : Memory) (pairs : List Ts) (s : St) (pw w0 w1 : Word)
    (a : Address) (deps : List WeakMem.Reg) (rel : Bool) (h0 : NV L w0.val) (h1 : NV L w1.val) :
    WrVM L mem s.promises
      (Promises.stepStorePair mem pairs (mth s pw w0 w1) a (dataE 1 w0) (dataE 2 w1) deps rel).1
      (Promises.stepStorePair mem pairs (mth s pw w0 w1) a (dataE 1 w0) (dataE 2 w1) deps rel).2.2.promises := by
  have e0 := rmwNewVal_dataE1 s pw w0 w1
  have e1 := rmwNewVal_dataE2 s pw w0 w1
  simp only [Promises.stepStorePair]
  refine WrVM.trans (WrVM.push _ ?_) (WrVM.push _ ?_)
  · show NV L (Promises.rmwNewVal (mth s pw w0 w1).regs (dataE 1 w0))
    rw [e0]; exact h0
  · show NV L (Promises.rmwNewVal (mth s pw w0 w1).regs (dataE 2 w1))
    rw [e1]; exact h1

theorem stepRmwPair_wrV_at {L : AllocLabel → Prop} {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : WeakMem.Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hv0 : NV L (Promises.rmwNewVal th.regs new0)) (hv1 : NV L (Promises.rmwNewVal th.regs new1)) :
    WrVM L mem th.promises mem' th'.promises := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [lock_promises]
    exact WrVM.refl _ _ _
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [lock_promises]
      exact WrVM.trans (WrVM.push _ hv0) (WrVM.push _ hv1)
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm1 : mem[tw + 1]? with
    | none => simp [hm, hm1] at hf
    | some pm1 =>
    simp only [hm, hm1, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hc, rfl, rfl, rfl⟩ := hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [lock_promises]
    exact WrVM.trans (WrVM.fulfil hm (by rw [hc.1.1.1.1.1.1.1.2]; exact hv0))
      (WrVM.fulfil hm1 (by rw [hc.1.1.1.1.2]; exact hv1))

theorem stepRmwPair_wrV {L : AllocLabel → Prop} {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : WeakMem.Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hv0 : NV L (Promises.rmwNewVal th.regs new0)) (hv1 : NV L (Promises.rmwNewVal th.regs new1)) :
    WrVM L mem th.promises mem' th'.promises := by
  have hx := stepRmwPair_wrV_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [lockTh_regs]; exact hv0) (by rw [lockTh_regs]; exact hv1)
  rwa [lockTh_prom] at hx

theorem loadUnits_wrV {L : AllocLabel → Prop} {arch' : Arch} {pw : Word} {a : Address} {acq : Bool}
    {us : List Acc} {n : Nat} {s : St} {r : St × List Word} (hr : r ∈ loadUnits arch' pw a acq us n s) :
    WrV L s r.1 := by
  obtain ⟨e1, -, e3⟩ := TermFul.loadUnits_keep us n s r hr
  show WrVM L s.mem s.promises r.1.mem r.1.promises
  rw [e1, e3]
  exact WrVM.refl _ _ _

theorem storeUnits_wrV {L : AllocLabel → Prop} {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address}
    {rel : Bool} : ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St),
      s' ∈ storeUnits k arch pw a rel us ws i s → AllNV L ws → WrV L s s'
  | [], _, _, s, s', hs, _ => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact WrV.refl _ _
  | .one :: us, w :: ws, i, s, s', hs, hw => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact WrVM.trans (stepStore_mth hst (allNV_head hw)) (storeUnits_wrV us ws (i + 1) _ s' hs (allNV_tail hw))
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hw => by
      simp only [storeUnits] at hs
      have h2 := stepStorePair_mth (L := L) s.mem s.pairs s pw w0 w1 (offs a i) [0] rel (allNV_head hw)
        (allNV_head (allNV_tail hw))
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs
      obtain ⟨mem', pairs', th⟩ := R
      exact WrVM.trans h2 (storeUnits_wrV us ws (i + 2) _ s' hs (allNV_tail (allNV_tail hw)))
  | .one :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _ => by simp [storeUnits] at hs

theorem fenceS_wrV (L : AllocLabel → Prop) (s : St) (f : WeakMem.Fence) : WrV L s (fenceS s f) :=
  WrVM.refl _ _ _

theorem allocBuf_wrV {L : AllocLabel → Prop} (lbl : AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val))
    (s : St) (hz : ∀ zs, zero = some zs → ∀ v ∈ zs, NV L v) : WrV L s (allocBuf lbl n zero s).1 := by
  unfold allocBuf
  refine WrVM.fold n _ fun j => ?_
  dsimp only
  cases zero with
  | none => exact nv_undef _
  | some l =>
      cases l with
      | nil => exact nv_undef _
      | cons z zs =>
          dsimp only
          rw [List.getD_eq_getElem?_getD]
          cases hg : (z :: zs)[j % (z :: zs).length]? with
          | none => exact nv_undef _
          | some v => exact hz _ rfl v (List.mem_of_getElem? hg)

theorem alloc_wrV {L : AllocLabel → Prop} {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) (hw : AllNV L ws) :
    WrV L s r.1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact WrVM.trans (WrVM.fold _ _ fun _ => nv_undef _) (storeUnits_wrV us ws 0 _ s' hs hw)

theorem nv_fetch (L : AllocLabel → Prop) (o : FetchOp) (x y : WeakMem.Val) : NV L (o.kind.apply x y) := by
  cases o <;> cases x <;> cases y <;> first | exact nv_num _ _ | exact nv_undef _

theorem injM_wrV {L : AllocLabel → Prop} {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word}
    {r : St × List Word} (h : r ∈ injM g s ty j p) (hp : AllNV L p) : WrV L s r.1 := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_wrV hs (allNV_cons (nv_num _ _) hp)
      dsimp only
      split
      · exact WrV.trans this (fenceS_wrV _ _ _)
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact WrV.refl _ _

theorem projM_wrV {L : AllocLabel → Prop} {g : G} {s : St} {ty : Ty} {ws : List Word}
    {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) : WrV L s r.1 := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 : WrV L s s1 := loadUnits_wrV h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact WrV.trans d1 (loadUnits_wrV h2))
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact WrV.refl _ _

theorem encodeArm_nv {L : AllocLabel → Prop} {tr : Tier} {as : List Ty} {j : Nat} {p out : List Word}
    (h : encodeArm tr as j p = some out) (hp : AllNV L p) : AllNV L out := by
  cases tr with
  | boxed => simp [encodeArm] at h
  | wide =>
      simp only [encodeArm] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact allNV_cons (nv_num _ _) (allNV_cons (nv_num _ _) (allNV_nil _))
      · simp only [Option.some.injEq] at h; subst h
        exact allNV_cons (nv_num _ _) (allNV_cons (allNV_head hp) (allNV_nil _))
      · cases h
  | niche =>
      simp only [encodeArm, bind, Option.bind] at h
      cases hj : as[j]? with
      | none => simp [hj] at h
      | some arm =>
          simp only [hj] at h
          generalize armK arm = k at h
          cases k <;> rcases p with _ | ⟨w, _ | ⟨w1, ps⟩⟩ <;> simp only at h
          all_goals first
            | (cases h; done)
            | (simp only [Option.some.injEq] at h; subst h; exact allNV_cons (nv_num _ _) (allNV_nil _))
            | (cases hv : w.val <;> simp [hv] at h
               all_goals first
                 | (obtain ⟨-, rfl⟩ := h; exact allNV_cons (nv_num _ _) (allNV_nil _))
                 | (subst h
                    refine allNV_cons ?_ (allNV_nil _)
                    intro a g e
                    simp only [WeakMem.Val.loc.injEq] at e
                    obtain ⟨rfl, -⟩ := e
                    exact hp w (List.mem_singleton_self _) _ _ hv))

theorem decodeArm_nv {L : AllocLabel → Prop} {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat}
    {p : List Word} (h : decodeArm tr as ws = some (j, p)) (hw : AllNV L ws) : AllNV L p := by
  rcases ws with _ | ⟨w, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> cases tr <;> simp only [decodeArm] at h
  all_goals try (cases h; done)
  all_goals
    cases hv : w.val <;> simp only [hv, bind, pure, Option.bind_eq_some_iff] at h
    all_goals first
      | (cases h; done)
      | (obtain ⟨x, -, h⟩ := h
         repeat' split at h
         all_goals first
           | (cases h; done)
           | (simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              first
                | exact allNV_nil _
                | exact allNV_cons (nv_null _) (allNV_nil _)
                | exact allNV_cons (allNV_head (allNV_tail hw)) (allNV_nil _)
                | (refine allNV_cons ?_ (allNV_nil _)
                   intro a g e
                   simp only [WeakMem.Val.loc.injEq] at e
                   obtain ⟨rfl, -⟩ := e
                   exact allNV_head hw _ _ hv)))

theorem asArm_nv {L : AllocLabel → Prop} {t : Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : asArm t ws = some (j, p)) (hw : AllNV L ws) : AllNV L p := by
  unfold asArm at h
  split at h
  · exact decodeArm_nv h hw
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hw

theorem ofArm_nv {L : AllocLabel → Prop} {t : Ty} {j : Nat} {p q : List Word}
    (h : ofArm t j p = some q) (hp : AllNV L p) : AllNV L q := by
  unfold ofArm at h
  split at h
  · exact encodeArm_nv h hp
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact hp
    · cases h

theorem zeroWords_nv (L : AllocLabel → Prop) (t : Ty) (vs : List WeakMem.Val) (h : zeroWords t = some vs) :
    ∀ v ∈ vs, NV L v := by
  cases t with
  | prod a b =>
      rw [zeroWords] at h
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      intro v hv
      simp only [List.mem_append] at hv
      rcases hv with hv | hv
      · exact zeroWords_nv L a x hx v hv
      · exact zeroWords_nv L b y hy v hv
  | refine t _ => rw [zeroWords] at h; exact zeroWords_nv L t vs h
  | iall t => rw [zeroWords] at h; exact zeroWords_nv L t vs h
  | iex t => rw [zeroWords] at h; exact zeroWords_nv L t vs h
  | mu t => rw [zeroWords] at h; exact zeroWords_nv L t vs h
  | sum a b =>
      rw [zeroWords] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i arm ha
          simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨p, hp, ws, he, rfl⟩ := h
          intro v hv
          simp only [List.mem_map] at hv
          obtain ⟨w, hw, rfl⟩ := hv
          have hlt : sizeOf arm < sizeOf (Ty.sum a b) := armsOf_getElem_lt ha
          have ih := zeroWords_nv L arm p hp
          refine encodeArm_nv he (fun u hu => ?_) w hw
          simp only [List.mem_map] at hu
          obtain ⟨z, hz, rfl⟩ := hu
          exact ih z hz
  | loc μ c =>
      cases c <;> simp [zeroWords] at h
      subst h
      intro v hv
      simp only [List.mem_singleton] at hv
      subst hv
      exact nv_null _
  | _ =>
      simp [zeroWords] at h
      all_goals
        subst h
        intro v hv
        simp only [List.mem_singleton, List.not_mem_nil] at hv <;> subst hv <;>
          first | exact nv_num _ _ | exact nv_null _
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals (try subst_vars)
  all_goals first
    | assumption
    | (simp <;> omega)

/-- The words of an atom name only `L`. -/
def AtNV (L : AllocLabel → Prop) (env : Env) (a : At) : Prop :=
  ∀ t ws, evalAt env a = some (t, ws) → AllNV L ws

/-- The payloads a projection of atom `a` returns, in a state with promises above coherence
(`PromAbove`), name only `L`. -/
def ProjNV (L : AllocLabel → Prop) (g : G) (env : Env) (s : St) (a : At) : Prop :=
  ∀ t ws, evalAt env a = some (t, ws) → ∀ r ∈ projM g s t ws, PromAbove r.1 → AllNV L r.2.2

theorem promLt_proj {g : G} {s : St} {ty : Ty} {ws : List Word} {r : St × Nat × List Word}
    (hpl : PromLt s) (h : r ∈ projM g s ty ws) : PromLt r.1 := by
  obtain ⟨e1, -, e3⟩ := TermFul.projM_keep h
  intro t ht
  rw [e1]
  exact hpl t (by rw [← e3]; exact ht)

/-- What an operation may write names only `L`: its stored operands and, for an injection, the
projected payload. -/
def OpWOK (L : AllocLabel → Prop) (g : G) (env : Env) (s : St) : Op → Prop
  | .new a => AtNV L env a
  | .store _ _ v _ => AtNV L env v
  | .stp _ _ v0 v1 _ => AtNV L env v0 ∧ AtNV L env v1
  | .xchg _ v => AtNV L env v
  | .xchgAt _ _ v => AtNV L env v
  | .xchgAtF _ _ _ v => AtNV L env v
  | .bufInit _ _ x => AtNV L env x
  | .inl _ a => ProjNV L g env s a
  | .inr _ a => ProjNV L g env s a
  | _ => True

theorem evalOp_wrV {L : AllocLabel → Prop} {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) (hw : OpWOK L g env s op) (hpl : PromLt s)
    (hpa : PromAbove r.1) : WrV L s r.1 := by
  cases op <;> simp only [OpWOK] at hw <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first
         | exact WrV.refl _ _
         | exact fenceS_wrV _ _ _
         | (dsimp only
            exact allocBuf_wrV _ _ _ _ (fun zs e => by
              first
                | exact zeroWords_nv L _ zs e
                | cases e
                | (split at e
                   · exact zeroWords_nv L _ zs e
                   · cases e))))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_wrV hx
         | exact storeUnits_wrV _ _ _ _ _ hx (hw _ _ (by assumption))
         | exact storeUnits_wrV _ _ _ _ _ hx
             (allNV_append (hw.1 _ _ (by assumption)) (hw.2 _ _ (by assumption)))
         | exact alloc_wrV hx (hw _ _ (by assumption))
         | exact stepRmw_wrV (th := mth s _ _ _) hx (fun _ => nv_fetch _ _ _ _))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact WrV.trans (projM_wrV hx)
             (injM_wrV hy (hw _ _ (by assumption) _ hx (injM_pa (promLt_proj hpl hx) hy hpa)))
         | exact WrV.trans (loadUnits_wrV hx) (storeUnits_wrV _ _ _ _ _ hy (hw _ _ (by assumption))))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 : WrV L s x.1 := loadUnits_wrV hx
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact WrV.trans d1 (storeUnits_wrV _ _ _ _ _ hy (allNV_cons (nv_num _ _) (allNV_nil _)))
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 : WrV L s x.1 := loadUnits_wrV hx
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)

/-- What a thread step may write names only `L`. -/
def TermWOK (L : AllocLabel → Prop) (g : G) (s : St) (th : TTh) : Prop :=
  match th.term with
  | .let_ _ op _ => OpWOK L g th.env s op
  | .case a _ _ _ _ => ProjNV L g th.env s a
  | .cas _ _ _ _ v _ _ _ => AtNV L th.env v
  | .casp _ _ _ _ _ v0 v1 _ _ _ => AtNV L th.env v0 ∧ AtNV L th.env v1
  | _ => True

/-- **A thread step's new non-promise messages hold values naming only `L`.** -/
theorem tstep_wrV {L : AllocLabel → Prop} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) (hw : TermWOK L g (stOf mem pairs th) th)
    (hpl : PromLt (stOf mem pairs th)) (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    WrV L (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold TermWOK at hw
  simp only [tstep] at h
  split at h
  all_goals (rename_i heq; simp only [heq] at hw)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact WrV.refl _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨-, h1⟩ := enter_eq he
       show WrVM L mem th.promises mem th'.promises
       rw [h1]; exact WrVM.refl _ _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨-, h1⟩ := enter_eq he
       show WrVM L mem th.promises mem th'.promises
       rw [h1]; exact WrVM.refl _ _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_wrV hx hw hpl hpa
         | exact stepRmw_wrV (th := mth _ _ _ _) hx (fun _ => nv_apply _ _ (by
             rw [rmwNewVal_dataE1]; exact allNV_head (hw _ _ (by assumption))))
         | exact stepRmwPair_wrV (th := mth _ _ _ _) hx
             (by rw [rmwNewVal_dataE1]; exact allNV_head (hw.1 _ _ (by assumption)))
             (by rw [rmwNewVal_dataE2]; exact allNV_head (hw.2 _ _ (by assumption))))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact WrV.trans (projM_wrV hx)
         (injM_wrV hy (hw _ _ (by assumption) _ hx (injM_pa (promLt_proj hpl hx) hy hpa))))
    | (simp only [List.mem_singleton] at h; subst h; exact fenceS_wrV _ _ .st)

/-! ## §2 Typed operands name allocated labels -/

theorem NV.mono {L L' : AllocLabel → Prop} (f : ∀ l, L l → L' l) {v : WeakMem.Val} (h : NV L v) : NV L' v :=
  fun a g e => f _ (h a g e)

theorem AllNV.mono {L L' : AllocLabel → Prop} (f : ∀ l, L l → L' l) {ws : List Word} (h : AllNV L ws) :
    AllNV L' ws := fun w hw => NV.mono f (h w hw)

theorem allNV_wle {L : AllocLabel → Prop} : ∀ {p q : List Word}, WLe p q → AllNV L p → AllNV L q
  | [], [], _, _ => allNV_nil _
  | w :: ws, w' :: ws', h, hp => by
      obtain ⟨h1, h2⟩ := h
      refine allNV_cons ?_ (allNV_wle h2 (allNV_tail hp))
      rw [← h1.1]; exact allNV_head hp
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- The labels `η` allocates: a cell or a box. -/
def Alloc (η : TEnv) (l : AllocLabel) : Prop := (∃ c, η.sto l = some c) ∨ ∃ B, η.box l = some B

/-- **A typed value's reference words name allocated labels** (closed by `VR_close`, then `noJunkA`). -/
theorem vr_named {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {t rt : Ty} {ws : List Word}
    (hE : EnvOK p η) (hW : WitL σs η.wit cx.opq) (hK : cx.ke.length ≤ σs.length)
    (ho : cx.opaqueOK t = true) (htb : tb cx.ke.length t = true) (hv : VR ρ η t (shp rt) ws)
    (hl : Lay σs t rt ws) : AllNV (Alloc η) ws := by
  have hsig : sig rt = sig (cl ρ η.wit 0 0 t) := lay_closed hW hK ho htb hl
  have hvc : VR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 t) (shp (cl ρ η.wit 0 0 t)) ws := by
    rw [← shp_of_sig hsig]
    exact (VR_close hE.2.1 ρ t [] 0 ρ (fun _ => 0) (shp rt) ws (fun _ => rfl)
      (fun _ hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨us, hus⟩ : ∃ us, accs rt = some us := by
    cases h : accs rt with
    | none => exact absurd (by simp [wc, h]) hl.2.2.1
    | some us => exact ⟨us, rfl⟩
  have hlen : ws.length = nWords us := hl.1 us hus
  have hwc : wc (cl ρ η.wit 0 0 t) = some ws.length := by
    rw [← wc_of_sig hsig, hlen]; simp [wc, hus]
  have hlab := noJunkA _ (CE η) _ ws hwc (Valid_lnorm _ _ (Valid_of_sig hsig hl.2.2.2.1)) hvc
  intro w hw a g e
  exact hlab w hw a g e

/-- A peeked atom's words name allocated labels. -/
theorem atNV_peek {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {a : At} {t : Ty} (hE : EnvOK p η) (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) : AtNV (Alloc η) env a := by
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi.2.1 hp
  intro t' ws' he
  rw [hea] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact vr_named hE hi.2.2.2.1 hi.2.2.2.2.1 (peek_opaqueOK htv hp) (peek_tb htv hp) hv hl

theorem atNV_use {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx c₁ : Cx}
    {env : Env} {a : At} {t : Ty} (hE : EnvOK p η) (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : cx.use a = .ok (t, c₁)) : AtNV (Alloc η) env a :=
  atNV_peek hE hi htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1

theorem atNV_idx {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {a : At} {j : Idx} (hE : EnvOK p η) (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hj : IntIdx cx a j) : AtNV (Alloc η) env a := by
  obtain ⟨t, hp, -⟩ := hj
  exact atNV_peek hE hi htv hp

theorem atNV_use1 {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₁ c₂ : Cx} {env : Env} {b a : At} {t t' : Ty} (hE : EnvOK p η) (hi : FInv ρ η σs K cx env)
    (htv : TvOK cx) (hb : cx.use b = .ok (t, c₁)) (hu : c₁.use a = .ok (t', c₂)) : AtNV (Alloc η) env a :=
  atNV_use hE (use_FInv hb hi).1 (use_TvOK hb htv).1 hu

theorem atNV_idx1 {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₁ : Cx} {env : Env} {b a : At} {t : Ty} {j : Idx} (hE : EnvOK p η) (hi : FInv ρ η σs K cx env)
    (htv : TvOK cx) (hb : cx.use b = .ok (t, c₁)) (hj : IntIdx c₁ a j) : AtNV (Alloc η) env a :=
  atNV_idx hE (use_FInv hb hi).1 (use_TvOK hb htv).1 hj

theorem AtNV.mono {L L' : AllocLabel → Prop} (f : ∀ l, L l → L' l) {env : Env} {a : At} (h : AtNV L env a) :
    AtNV L' env a := fun t ws he => AllNV.mono f (h t ws he)

/-- **A used atom's projections name `L`**: unboxed, the payload is among the operand's words;
boxed, it is the operand box's payload (`projM_own`, under `PromAbove`). -/
theorem projNV_use {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₁ : Cx} {env : Env} {s : St} {a : At} {t : Ty} {L : AllocLabel → Prop} (hE : EnvOK p η)
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx) (hbi : BoxInv g (CE η) s) (hu : cx.use a = .ok (t, c₁))
    (hL1 : ∀ l, Alloc η l → L l) (hL2 : ∀ l B, η.box l = some B → AllNV L B.pay) : ProjNV L g env s a := by
  obtain ⟨-, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
  have hp := (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 t) :=
    lay_closed hi.2.2.2.1 hi.2.2.2.2.1 (peek_opaqueOK htv hp) htb hl
  have hws : AllNV L ws :=
    AllNV.mono hL1 (vr_named hE hi.2.2.2.1 hi.2.2.2.2.1 (peek_opaqueOK htv hp) htb hv hl)
  intro t' ws' he r hr hpa
  rw [hea] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  cases hrb : isBoxed rt
  · rw [projM_nbB hrb] at hr
    simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at hr
    obtain ⟨⟨j, q⟩, hq, rfl⟩ := hr
    exact asArm_nv hq hws
  · obtain ⟨w, x, B, arm, us, rfl, hw, hx0, hB, harm, hus, hnw, -, -, hsee⟩ :=
      boxed_operand hE.2.1 hbi hrb hsig hv
    obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee hrb hw hx0 hB harm hus hnw.symm
    obtain ⟨-, hWp, -⟩ := (hpr r hr).2 hpa
    exact allNV_wle hWp (hL2 _ _ hB)

/-- **A typed thread's writes name `L`** (`TermWOK`), for any `L` containing the labels `η`
allocates and the labels of `η`'s box payloads. -/
theorem termWOK_of {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {L : AllocLabel → Prop}
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hL1 : ∀ l, Alloc η l → L l) (hL2 : ∀ l B, η.box l = some B → AllNV L B.pay) :
    TermWOK L g (stOf mem pairs th) th := by
  have hbi : BoxInv g (CE η) (stOf mem pairs th) := hm.2.2.2.2.2.2.2.2.2.1
  have W1 : ∀ {a : At} {t : Ty} {c₁ : Cx}, cx.use a = .ok (t, c₁) → AtNV L th.env a :=
    fun hu => AtNV.mono hL1 (atNV_use hE hi htv hu)
  have W2 : ∀ {a : At} {j : Idx}, IntIdx cx a j → AtNV L th.env a :=
    fun hj => AtNV.mono hL1 (atNV_idx hE hi htv hj)
  have W3 : ∀ {b a : At} {t t' : Ty} {c₁ c₂ : Cx}, cx.use b = .ok (t, c₁) → c₁.use a = .ok (t', c₂) →
      AtNV L th.env a :=
    fun hb hu => AtNV.mono hL1 (atNV_use1 hE hi htv hb hu)
  have W4 : ∀ {b a : At} {t : Ty} {c₁ : Cx} {j : Idx}, cx.use b = .ok (t, c₁) → IntIdx c₁ a j →
      AtNV L th.env a :=
    fun hb hj => AtNV.mono hL1 (atNV_idx1 hE hi htv hb hj)
  have WP : ∀ {a : At} {t : Ty} {c₁ : Cx}, cx.use a = .ok (t, c₁) → ProjNV L g th.env (stOf mem pairs th) a :=
    fun hu => projNV_use hE hi htv hbi hu hL1 hL2
  unfold TermWOK
  cases hterm : th.term with
  | let_ x op e =>
      rw [hterm] at hT
      cases hT with
      | let_ hop he =>
          cases hop
          all_goals (try simp only [OpWOK])
          all_goals first
            | trivial
            | exact WP (by assumption)
            | exact W1 (by assumption)
            | exact W2 (by assumption)
            | exact W3 (by assumption) (by assumption)
            | exact W4 (by assumption) (by assumption)
            | exact ⟨W2 (by assumption), W2 (by assumption)⟩
            | exact ⟨W4 (by assumption) (by assumption), W4 (by assumption) (by assumption)⟩
  | case a x e₁ y e₂ =>
      rw [hterm] at hT
      cases hT with
      | case hu _ _ _ _ => exact WP hu
  | cas acq rel w e v t ok fail =>
      rw [hterm] at hT
      cases hT
      all_goals first
        | exact W1 (by assumption)
        | exact W2 (by assumption)
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
      rw [hterm] at hT
      cases hT
      all_goals exact ⟨W2 (by assumption), W2 (by assumption)⟩
  | _ => trivial

/-! ## §3 `bnamedT` -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- `E_g`'s allocated labels. -/
def GAlloc (Eg : GEnv) (l : AllocLabel) : Prop := (∃ c, Eg.sto l = some c) ∨ ∃ B, Eg.box l = some B

/-- **(T18) Box payloads stay named across a thread step.**  An old box keeps its payload, named
in `E_g` (`SysInvN.bnamed`) at labels the step does not take.  A new box's words are latest
non-promise messages at its fresh label (post `BoxTopP` of the `TOut` witness), where every old
message is a promise (`SysInvN.fresh`); so they were written by the step (`tstep_wrV`), whose
writes are typed operands or old boxes' payloads (`termWOK_of`), all naming `E_g`'s labels. -/
theorem bnamedT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      GBoxNamed (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X _ Z
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce0, hE2, hT2, htv2, hi2, -⟩ := hRE0
  have hce2 : CE η2 = Cut Eg i S0 := hce0
  have hm : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce0]; exact hm0
  have hL1 : ∀ l, Alloc η2 l → GAlloc Eg l := by
    intro l h
    rcases h with ⟨c1, h⟩ | ⟨B, h⟩
    · have h' : (Cut Eg i S0).sto l = some c1 := by rw [← hce2]; exact h
      exact Or.inl ⟨c1, (cutSto_some.1 h').1⟩
    · have h' : (Cut Eg i S0).box l = some B := by rw [← hce2]; exact h
      exact Or.inr ⟨B, h'⟩
  have hL2 : ∀ l B, η2.box l = some B → AllNV (GAlloc Eg) B.pay := by
    intro l B h w hw a g e
    have h' : (Cut Eg i S0).box l = some B := by rw [← hce2]; exact h
    exact X.inv.bnamed l B h' w hw a g e
  have hw := termWOK_of hT2.1 hi2.1 hE2 htv2 hm hL1 hL2
  have hpa : PromAbove (stOf r.1 r.2.1 r.2.2) := by
    have h1 := TermTyped.certified_promAboveSt X.cert X.e3
    rw [X.e1, X.e2] at h1
    exact h1
  have hwr := tstep_wrV X.hr hw hm.2.2.1 hpa
  -- labels `E_g` allocates are not the step's fresh labels
  have hnf : ∀ l, GAlloc Eg l → ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := by
    rintro l hl ⟨j, hj, -, e⟩
    obtain ⟨h1, h2, -⟩ := X.inv.fresh i th X.hth j hj
    subst e
    rcases hl with ⟨c1, hc⟩ | ⟨B, hB⟩
    · have e := h1.symm.trans hc
      cases e
    · have e := h2.symm.trans hB
      cases e
  have hout : ∀ l, GAlloc Eg l →
      (∃ c1, (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some c1) ∨
        ∃ B', (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B' := by
    intro l hl
    have hf := hnf l hl
    simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte]
    exact hl
  intro l B hB w hwB a g e
  by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · have hB' : E'.box l = some B := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    have hbt := Z.2.2.1.2.2.2.2.2.2.2.2.2.1.2.1 l B hB'
    obtain ⟨o, ho⟩ := List.mem_iff_getElem?.1 hwB
    obtain ⟨t, -, ⟨m, hmt, hml, hmv, -⟩, hns, -⟩ := hbt.2 o w ho
    rcases hwr t m hmt hns with ⟨hold, hnp⟩ | hnv
    · obtain ⟨j, hj, -, el⟩ := hf
      have hpr := (X.inv.fresh i th X.hth j hj).2.2.2.2 t m hold (by rw [hml, el]; rfl)
      exact absurd hpr hnp
    · exact hout _ (hnv a g (hmv.trans e))
  · have hB' : Eg.box l = some B := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    exact hout _ (X.inv.bnamed l B hB' w hwB a g e)

end

end TermBNamed

#print axioms TermBNamed.tstep_wrV
#print axioms TermBNamed.evalOp_wrV
#print axioms TermBNamed.zeroWords_nv
#print axioms TermBNamed.vr_named
#print axioms TermBNamed.projNV_use
#print axioms TermBNamed.termWOK_of
#print axioms TermBNamed.bnamedT_of
