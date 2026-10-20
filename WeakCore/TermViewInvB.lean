import WeakCore.TermViewInv

/-!
# TermViewInvB: the term layer's memory primitives keep `StV`, and their words are `WV`
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem WV_view {n : Nat} {w : Word} (h : WV n w) : w.view ≤ n := Nat.le_trans h.1 h.2

theorem mth_regs {s : St} {n : Nat} {r0 r1 r2 : Word} (h0 : WV n r0) (h1 : WV n r1) (h2 : WV n r2) :
    ∀ r, ((mth s r0 r1 r2).regs r).view ≤ n := fun r => WV_view (regsOf_WV h0 h1 h2 r)

theorem StV_vs {s : St} (hs : StV s) {th : Promises.Thread} (hv : VSB s.mem.size th.vs) (u : Nat) :
    StV { s with vs := th.vs, undefs := u } := ⟨hs.1, hv⟩

theorem loadUnits_V {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s s' : St) (ws : List Word),
    (s', ws) ∈ loadUnits arch pw a acq us k s → StV s → WV s.mem.size pw →
    StV s' ∧ s'.mem = s.mem ∧ WsV s.mem.size ws
  | [], k, s, s', ws, h, hs, _ => by
      simp only [loadUnits, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs, rfl, WsV_nil _⟩
  | .one :: us, k, s, s', ws, h, hs, hp => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, hth, ⟨s1, ws1⟩, hin, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hvs, hw, -⟩ := stepLoad_V hs.1 hs.2 hth
      obtain ⟨h1, h2, h3⟩ := loadUnits_V us (k + 1) _ s1 ws1 hin (StV_vs hs hvs _) hp
      exact ⟨h1, h2, WsV_cons hw h3⟩
  | .two :: us, k, s, s', ws, h, hs, hp => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, hth, ⟨s1, ws1⟩, hin, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hvs, hw0, hw1, -⟩ := stepLoadPair_V hs.1 hs.2 hth
      obtain ⟨h1, h2, h3⟩ := loadUnits_V us (k + 2) _ s1 ws1 hin (StV_vs hs hvs _) hp
      exact ⟨h1, h2, WsV_cons hw0 (WsV_cons hw1 h3)⟩

theorem storeUnits_V {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St),
    s' ∈ storeUnits k arch pw a rel us ws i s → StV s → WV s.mem.size pw → WsV s.mem.size ws →
    StV s' ∧ s.mem.size ≤ s'.mem.size
  | [], _, i, s, s', h, hs, _, _ => by
      simp only [storeUnits, List.mem_singleton] at h
      subst h; exact ⟨hs, Nat.le_refl _⟩
  | .one :: us, [], i, s, s', h, _, _, _ => by simp [storeUnits] at h
  | .one :: us, w :: ws, i, s, s', h, hs, hp, hw => by
      simp only [storeUnits, List.mem_flatMap] at h
      obtain ⟨⟨mem', th⟩, hst, hin⟩ := h
      have hw0 := hw w (by simp)
      obtain ⟨hm', hle, hvs', -⟩ := stepStore_V hs.1 hs.2 (mth_regs hp hw0 hw0) hst
      have hs1 : StV { s with mem := mem', vs := th.vs, promises := th.promises } := ⟨hm', hvs'⟩
      obtain ⟨h1, h2⟩ := storeUnits_V us ws (i + 1) _ s' hin hs1 (hp.mono hle)
        ((fun x hx => hw x (by simp [hx])) |> fun h => WsV.mono h hle)
      exact ⟨h1, Nat.le_trans hle h2⟩
  | .two :: us, [], i, s, s', h, _, _, _ => by simp [storeUnits] at h
  | .two :: us, [_], i, s, s', h, _, _, _ => by simp [storeUnits] at h
  | .two :: us, w0 :: w1 :: ws, i, s, s', h, hs, hp, hw => by
      simp only [storeUnits] at h
      generalize hq : Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel = q at h
      obtain ⟨mem', pairs', th⟩ := q
      have hw0 := hw w0 (by simp)
      have hw1 := hw w1 (by simp)
      obtain ⟨hm', hle, hvs', -⟩ := stepStorePair_V hs.1 hs.2 (mth_regs hp hw0 hw1) hq
      have hs1 : StV { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises } :=
        ⟨hm', hvs'⟩
      obtain ⟨h1, h2⟩ := storeUnits_V us ws (i + 2) _ s' h hs1 (hp.mono hle)
        ((fun x hx => hw x (by simp [hx])) |> fun h => WsV.mono h hle)
      exact ⟨h1, Nat.le_trans hle h2⟩

theorem foldl_push_V (f : Nat → Msg) (hf : ∀ j, (f j).view = 0) :
    ∀ (l : List Nat) (mem : Memory), MsgV mem →
      MsgV (l.foldl (fun m j => m.push (f j)) mem) ∧ (l.foldl (fun m j => m.push (f j)) mem).size = mem.size + l.length
  | [], mem, h => ⟨h, rfl⟩
  | j :: l, mem, h => by
      simp only [List.foldl_cons]
      obtain ⟨h1, h2⟩ := foldl_push_V f hf l (mem.push (f j)) (MsgV_push h (by rw [hf]; exact Nat.zero_le _))
      refine ⟨h1, ?_⟩
      rw [h2, Array.size_push, List.length_cons]; omega

theorem fenceS_V {s : St} (hs : StV s) (f : WeakMem.Fence) : StV (fenceS s f) ∧ (fenceS s f).mem = s.mem :=
  ⟨⟨hs.1, (stepFence_V (th := mth s (cst (.num 0)) (cst (.num 0)) (cst (.num 0))) hs.2 f).1⟩, rfl⟩

theorem alloc_V {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) (hs : StV s) (hw : WsV s.mem.size ws) :
    StV s' ∧ s.mem.size ≤ s'.mem.size ∧ WV s'.mem.size pw := by
  unfold alloc at h
  simp only [List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s1, hin, rfl, rfl⟩ := h
  have hfp := foldl_push_V (fun j => (⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩ : Msg)) (fun _ => rfl)
    (List.range (nWords us)) s.mem hs.1
  rw [List.length_range] at hfp
  have hle : s.mem.size ≤ s.mem.size + nWords us := Nat.le_add_right _ _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs.2
  have key := storeUnits_V us ws 0 _ s1 hin ?hS (WV_cst _ _) ?hW
  · exact ⟨key.1, Nat.le_trans (by rw [hfp.2]; exact hle) key.2, WV_cst _ _⟩
  case hS =>
    refine ⟨hfp.1, ?_⟩
    dsimp only
    rw [hfp.2]
    exact ⟨Nat.le_trans h1 hle, Nat.max_le.2 ⟨Nat.le_trans h2 hle, Nat.sub_le _ _⟩, Nat.le_trans h3 hle,
      Nat.le_trans h4 hle, Nat.le_trans h5 hle⟩
  case hW =>
    dsimp only
    rw [hfp.2]; exact hw.mono hle

/-- The first value `allocBuf` writes at word `j`. -/
def allocVal (zero : Option (List Val)) (j : Nat) : Val :=
  match zero with
  | some (z :: zs) => (z :: zs).getD (j % (z :: zs).length) .undef
  | _ => .undef

theorem allocBuf_mem (lbl : AllocLabel) (n : Nat) (z : Option (List Val)) (s : St) :
    (allocBuf lbl n z s).1.mem =
      (List.range n).foldl (fun m j => m.push ⟨offs ⟨lbl, 0⟩ j, allocVal z j, 0⟩) s.mem := by
  unfold allocBuf allocVal; rfl

theorem allocBuf_V {lbl : AllocLabel} {n : Nat} {z : Option (List Val)} {s : St} (hs : StV s) :
    StV (allocBuf lbl n z s).1 ∧ s.mem.size ≤ (allocBuf lbl n z s).1.mem.size ∧
      WV (allocBuf lbl n z s).1.mem.size (allocBuf lbl n z s).2 := by
  have hfp := foldl_push_V (fun j => (⟨offs ⟨lbl, 0⟩ j, allocVal z j, 0⟩ : Msg)) (fun _ => rfl)
    (List.range n) s.mem hs.1
  rw [List.length_range, ← allocBuf_mem] at hfp
  have hle : s.mem.size ≤ s.mem.size + n := Nat.le_add_right _ _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs.2
  have e1 : (allocBuf lbl n z s).1.vs.vRd = s.vs.vRd := rfl
  have e2 : (allocBuf lbl n z s).1.vs.vWr = max s.vs.vWr (s.mem.size + n - 1) := rfl
  have e3 : (allocBuf lbl n z s).1.vs.vCtrl = s.vs.vCtrl := rfl
  have e4 : (allocBuf lbl n z s).1.vs.vPreBase = s.vs.vPreBase := rfl
  have e5 : (allocBuf lbl n z s).1.vs.vRelSt = s.vs.vRelSt := rfl
  have e6 : (allocBuf lbl n z s).2 = cst (.loc ⟨lbl, 0⟩ 0) := rfl
  refine ⟨⟨hfp.1, ?_⟩, by rw [hfp.2]; exact hle, by rw [e6]; exact WV_cst _ _⟩
  rw [hfp.2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact Nat.le_trans h1 hle
  · rw [e2]; exact Nat.max_le.2 ⟨Nat.le_trans h2 hle, Nat.sub_le _ _⟩
  · rw [e3]; exact Nat.le_trans h3 hle
  · rw [e4]; exact Nat.le_trans h4 hle
  · rw [e5]; exact Nat.le_trans h5 hle

end TermViewInv
