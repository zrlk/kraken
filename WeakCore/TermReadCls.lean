import WeakCore.TermReadClsM
import WeakCore.TermOwnCLoad
import WeakCore.TermOverCrNP

/-! # TermReadCls: `ReadClsF`

A thread step raising the stepper's coherence at a unit `b` of its own frontier cell to an old
non-promise message reads `b` (`TermReadClsM.tstep_rd`).  The typed reads are classified
(`RdC`): `b` lies in a non-affine loaded component (`CompAff`: load family, `fetch`/`cas` of a
copyable one-word atom), or is a word unit, or a unit of an epoch pair (`EPairUnit`), or is
off Σ (a box, a fresh label).  In a non-word, non-epair unit of a Σ cell the first holds, and the
piece of the cell containing `b` lies inside the component (`TermOwnCLoad.piece_in_comp`), so it is
non-affine (`TermAffAt.affine_atOffA`).
-/

namespace TermReadCls

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermB5 TermForWU TermFul
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermReadClsM

/-- `a` is a unit of an epoch pair of its cell (either word). -/
def EPairUnit (E : TEnv) (a : Address) : Prop :=
  ∃ c, E.sto a.label = some c ∧ ∃ n P, AtOff c.ty a.offset (.epair (.lit n) P) ∨
    (1 ≤ a.offset ∧ AtOff c.ty (a.offset - 1) (.epair (.lit n) P))

theorem EPairUnit_congr {E E' : TEnv} {a : Address} (h : E'.sto a.label = E.sto a.label) :
    EPairUnit E' a ↔ EPairUnit E a := by
  unfold EPairUnit; rw [h]

/-- (for) **An epoch-pair unit is a word of a two-word unit** of its (laid-out) cell. -/
theorem epairUnit_twoAtT {E : TEnv} {l : AllocLabel} {o : Nat} {cl : Cell}
    (h : EPairUnit E ⟨l, o⟩) (hs : E.sto l = some cl) (hlay : LayT cl.ty) :
    ∃ q, TwoAtT cl.ty q ∧ (o = q ∨ o = q + 1) := by
  obtain ⟨c, hc, n, P, hat⟩ := h
  have e : c = cl := Option.some.inj (hc.symm.trans hs)
  subst e
  rcases hat with ha | ⟨h1, ha⟩
  · exact ⟨o, TermOverCrW.epair_twoAtT hlay ha, .inl rfl⟩
  · exact ⟨o - 1, TermOverCrW.epair_twoAtT hlay ha, .inr (by have h1' : 1 ≤ o := h1; omega)⟩

/-- A non-affine component at `b0` with units `us`. -/
def CompAff (E : TEnv) (b0 : Address) (us : List Acc) : Prop :=
  ∃ c U, E.sto b0.label = some c ∧ AtOff c.ty b0.offset U ∧ accs U = some us ∧ Ty.affine U = false

/-- **The read classification** at `b`. -/
def RdC (E : TEnv) (b : Address) : Prop :=
  (∃ b0 us j, CompAff E b0 us ∧ j < nWords us ∧ b = offs b0 (0 + j)) ∨ WordUnit E b ∨ EPairUnit E b ∨
    E.sto b.label = none

theorem RdC_congr {E E' : TEnv} {b : Address} (h : ∀ l, E'.sto l = E.sto l) (hr : RdC E b) : RdC E' b := by
  rcases hr with ⟨b0, us, j, ⟨c, U, hs, hat, hus, haf⟩, hj, hb⟩ | hw | hp | hn
  · exact .inl ⟨b0, us, j, ⟨c, U, by rw [h]; exact hs, hat, hus, haf⟩, hj, hb⟩
  · exact .inr (.inl ((WordUnit_congr (h _)).2 hw))
  · exact .inr (.inr (.inl ((EPairUnit_congr (h _)).2 hp)))
  · exact .inr (.inr (.inr (by rw [h]; exact hn)))

/-- **From a non-affine component to the piece**: in an own cell (`CellOK`), closed and guarded,
the piece containing a unit of a non-affine component is non-affine. -/
theorem readAt_goal {E : TEnv} {n : Nat} {cl : Cell} {vals : List Word} {b b0 : Address} {us : List Acc}
    {j : Nat} (hc : CellOK E n cl.ty vals) (hclo : Clo cl.ty) (hmg : mg cl.ty = true)
    (hsto : E.sto b.label = some cl) (hca : CompAff E b0 us) (hj : j < nWords us)
    (hb : b = offs b0 (0 + j)) :
    ∃ q V vs, TermPiece.Piece cl.ty q V ∧ accs V = some vs ∧ q ≤ b.offset ∧ b.offset < q + nWords vs ∧
      Ty.affine V = false := by
  obtain ⟨c, U, hs0, hat, hus, haf⟩ := hca
  subst hb
  have e : c = cl := Option.some.inj (hs0.symm.trans hsto)
  subst e
  have hoff : (offs b0 (0 + j)).offset = b0.offset + j := by simp [offs]
  have cover : ∃ q V vs, TermPiece.Piece c.ty q V ∧ accs V = some vs ∧ q ≤ b0.offset + j ∧
      b0.offset + j < q + nWords vs := by
    rcases hc with ⟨hwc, -⟩ | ⟨N, e', us', hT, hus', -, -, -⟩
    · obtain ⟨L, hL, -⟩ := wc_some hwc
      have hbd := AtOff_bound hat hL hus
      exact TermPieceCov.piece_cover hclo hmg hL (by omega)
    · rcases AtOff_arr_elem hat hT with hU | ⟨us2, j2, o2, hus2, hj2, ho2, hat2⟩
      · rw [hU, hT] at hus; simp [accs] at hus
      · have hus2' : us2 = us' := Option.some.inj (hus2.symm.trans hus')
        subst hus2'
        have hbd := AtOff_bound hat2 hus2 hus
        have hle : (j2 + 1) * nWords us2 ≤ N * nWords us2 := Nat.mul_le_mul_right _ hj2
        rw [Nat.succ_mul] at hle
        have hclo' : Clo c.ty := hclo
        rw [hT] at hclo'
        have hmg' : mg e' = true := by have := hmg; rw [hT] at this; simpa [mg] using this
        have := TermPieceCov.piece_cover_arr (N := N) (o := b0.offset + j) (TermOverCrW.Clo_arr hclo') hmg' hus2
          (by omega)
        rw [hT]; exact this
  obtain ⟨q, V, vs, hP, hvs, h1, h2⟩ := cover
  have h3 : q < b0.offset + nWords us := by omega
  have h4 : b0.offset < q + nWords vs := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h2
  obtain ⟨-, hat2⟩ := TermOwnCLoad.piece_in_comp hat hus hP hvs h3 h4
  exact ⟨q, V, vs, hP, hvs, by rw [hoff]; exact h1, by rw [hoff]; exact h2,
    TermAffAt.affine_atOffA hat2 haf⟩

#print axioms readAt_goal

/-! ## Per-op classification -/

/-- A boxed operand's box is off Σ; so is the fresh label. -/
theorem box_none {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₁ : Cx} {env : Env} {s : St} {a : At} {t : Ty} {b : Address} (hE : EnvOK p η)
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx) (hm : MemInv g (CE η) s) (hu : cx.use a = .ok (t, c₁))
    (hB : BoxRd g env s a b) : (CE η).sto b.label = none := by
  rcases hB with ⟨t', pw, b0, hea', hrb, hb0, hl⟩ | hf
  · obtain ⟨-, rt, ws, hea, hv, hlay⟩ := use_FInv hu hi
    have hp := (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1
    have htb := (use_TvOK hu htv).2.1
    have hsig : sig rt = sig (cl ρ η.wit 0 0 t) :=
      lay_closed hi.2.2.2.1 hi.2.2.2.2.1 (peek_opaqueOK htv hp) htb hlay
    rw [hea] at hea'
    simp only [Option.some.injEq, Prod.mk.injEq] at hea'
    obtain ⟨rfl, rfl⟩ := hea'
    obtain ⟨w, x, B, arm, us, hws, hw, -, -, -, -, -, hnone, -⟩ :=
      boxed_operand hE.2.1 hm.2.2.2.2.2.2.2.2.2.1 hrb hsig hv
    simp only [List.cons.injEq, and_true] at hws
    subst hws
    have e : b0 = x := by simp [addrOf, hw] at hb0; exact hb0.symm
    subst e
    rw [hl]; exact hnone
  · rw [hf]; exact (hm.2.2.2.1.1 _ (Nat.le_refl _)).1

#print axioms box_none

/-- A pair reference (`ldp`, `casp`) reads word units or epoch-pair units. -/
theorem pair_rd {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t rt : Ty}
    {pw : Word} {b0 b : Address} (hvars : VarsOK ρ η σs cx.vars env) (hp : cx.peek a = .ok t)
    (hsc : ∃ μ u, (t = .ptr μ u ∨ t = .loc μ u) ∧ (μ = .own ∨ μ = .pub) ∧
      ((∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P)))
    (hea : evalAt env a = some (rt, [pw])) (hb0 : addrOf pw = some b0) (hb : b = b0 ∨ b = b0.next) :
    WordUnit (CE η) b ∨ EPairUnit (CE η) b := by
  obtain ⟨μ, u, ht, -, ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩⟩ := hsc
  · obtain ⟨c, n, hsto, hat⟩ := word2_tgt hvars hp ht hea hb0
    rcases hb with rfl | rfl
    · exact .inl ⟨c, hsto, .inr (.inl ⟨_, _, hat⟩)⟩
    · exact .inl ⟨c, hsto, .inr (.inr ⟨_, _, by simp [WeakMem.Address.next],
        by simpa [WeakMem.Address.next] using hat⟩)⟩
  · obtain ⟨c, n, hsto, hat⟩ := epair_tgt hvars hp ht hea hb0
    rcases hb with rfl | rfl
    · exact .inr ⟨c, hsto, _, _, .inl hat⟩
    · exact .inr ⟨c, hsto, _, _, .inr ⟨by simp [WeakMem.Address.next],
        by simpa [WeakMem.Address.next] using hat⟩⟩

#print axioms pair_rd

theorem offs_zero (b : Address) : offs b (0 + 0) = b := by cases b; simp [offs]

/-- An RMW target (`fetch`/`cas`): a word unit or a non-affine one-word component. -/
theorem rmw_rdC {E : TEnv} {b : Address} (h : WordUnit E b ∨ TermOwnCR5.RmwAtomC E b) : RdC E b := by
  rcases h with hw | ⟨c, S, hsto, hat, hS, -, -, haf⟩
  · exact .inr (.inl hw)
  · exact .inl ⟨b, [.one], 0, ⟨c, S, hsto, hat, hS, haf⟩, by simp [nWords, Acc.size], (offs_zero b).symm⟩


theorem load_rdC {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {acq : Bool} {a : At} {b : Address}
    (hop : OpT p cx x (.load acq a) c') (hsc : OpScope cx (.load acq a))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hrd : RdOp g env s (.load acq a) b) : RdC (CE η) b := by
  obtain ⟨rt, pw, μr, ru, b0, us, j, hea, hcr, hb0, hus, hj, hb⟩ := hrd
  have own : ∀ {t u : Ty} {μ : Mode}, cx.peek a = .ok t → cellOf t = some (μ, u) →
      Ty.affineIn cx.ke u = false → cx.opaqueOK u = true → RdC (CE η) b := by
    intro t u μ hp hc haf ho
    obtain ⟨c, U, hsto, hat, hFd⟩ := ptr_target hi.2.1 hp (cell_cases hc) hea hb0
    have hacc : accs U = some us := by
      rw [Fd_accs hFd, ← pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr,
        hus]
    have hVa := AffineCl.affine_cl0 ρ η.wit cx.ke (fun k => (hE.2.1 k).1)
      (fun k _ hk => hi.2.2.2.2.2.2.2.2.1 k hk) _ haf (tb_cellOf (peek_tb htv hp) hc)
    exact .inl ⟨b0, us, j, ⟨c, U, hsto, hat, hacc, TermAffAt.affine_fdA hFd hVa⟩, hj, hb⟩
  cases hop with
  | loadOwn hp _ hc haf hbind => exact own hp hc haf (bind_opaqueOK hbind)
  | loadPub hp _ hc haf _ hbind => exact own hp hc haf (bind_opaqueOK hbind)
  | loadRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | loadCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | loadTorn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | @loadWord _ _ _ _ tw rP hp hw hg _ =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb0
      have hc : cellOf tw = some (μ, Ty.word rP.1 rP.2) := by rcases ht with rfl | rfl <;> rfl
      have hacc := pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc
        (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr
      rw [hus] at hacc
      simp [cl, clI_zero, accs, hg] at hacc
      subst hacc
      have hj0 : j = 0 := by simp [nWords, Acc.size] at hj; omega
      subst hj0
      rw [offs_zero] at hb
      subst hb
      exact .inr (.inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩)

#print axioms load_rdC


theorem loadAt_rdC {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb i : At} {b : Address}
    (hop : OpT p cx x (.loadAt bb i) c') (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hrd : RdOp g env s (.loadAt bb i) b) : RdC (CE η) b := by
  obtain ⟨rt, pw, ti, iws, μ, u0, j0, a0, us, j, hea, hei, hbe, hnj, hb, hus, hj, hbb⟩ := hrd
  cases hop with
  | loadAt hp hbuf hint hlt hltk haf hbind =>
      obtain ⟨c, hsto, hat, hacc, htb⟩ :=
        buf_slot hi hE htv hp hbuf hint hlt hltk (bind_opaqueOK hbind) hea hei hbe hnj hb hus
      have hVa := AffineCl.affine_cl0 ρ η.wit cx.ke (fun k => (hE.2.1 k).1)
        (fun k _ hk => hi.2.2.2.2.2.2.2.2.1 k hk) _ haf htb
      exact .inl ⟨offs a0 (j0 * nWords us), _, j, ⟨c, _, hsto, hat, hacc, hVa⟩, hj, hbb⟩

#print axioms loadAt_rdC

theorem loadAtF_rdC {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb i : At} {q : List Nat} {b : Address}
    (hop : OpT p cx x (.loadAtF bb i q) c') (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hrd : RdOp g env s (.loadAtF bb i q) b) : RdC (CE η) b := by
  obtain ⟨rt, pw, ti, iws, μ, u0, j0, a0, us0, c0, o0, cs, j, hea, hei, hbe, hnj, hb, hus0, hco0, hcs, hj, hbb⟩ :=
    hrd
  cases hop with
  | loadAtF hp hbuf hct hopu hint hlt hltk haf hbind =>
      obtain ⟨cc, hsto, hat, hacc, htbc⟩ := bufF_slot hi hE htv hp hbuf hct hopu hint hlt hltk
        (bind_opaqueOK hbind) hea hei hbe hnj hb hus0 hco0 hcs
      have hVa := AffineCl.affine_cl0 ρ η.wit cx.ke (fun k => (hE.2.1 k).1)
        (fun k _ hk => hi.2.2.2.2.2.2.2.2.1 k hk) _ haf htbc
      exact .inl ⟨offs a0 (j0 * nWords us0 + o0), cs, j, ⟨cc, _, hsto, hat, hacc, hVa⟩, hj, hbb⟩

#print axioms loadAtF_rdC


theorem lanes_comp {E : TEnv} {c : Cell} {ad : Address} {k : Nat} {ρ : Nat → Nat} {W : Nat → Ty} {sg : Bool} {w : Wd}
    (hsto : E.sto ad.label = some c)
    (hat : AtOff c.ty (offs ad k).offset (cl ρ W 0 0 (.lanes sg w))) : CompAff E (offs ad k) [.one] :=
  ⟨c, _, hsto, hat, by simp [cl, accs], by simp [cl, Ty.affine, Ty.affineIn]⟩

theorem ldl_rdC {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb i : At} {b : Address}
    (hop : OpT p cx x (.ldl bb i) c') (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hrd : RdOp g env s (.ldl bb i) b) : RdC (CE η) b := by
  obtain ⟨rt, pw, t1, iws, μ0, u0, j0, a0, sg0, w0, jx, hea, hei, hbe, hnj, hb, hlo0, hjx, hbb⟩ := hrd
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk _ =>
      obtain ⟨c, hsto, hat⟩ :=
        lane_slotN hi htv ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩ hea hei hbe hnj hb hlo0
      exact .inl ⟨_, _, jx, lanes_comp hsto hat, hjx, hbb⟩

#print axioms ldl_rdC

theorem ldlw_rdC {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb wi jl : At} {b : Address}
    (hop : OpT p cx x (.ldlw bb wi jl) c') (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hrd : RdOp g env s (.ldlw bb wi jl) b) : RdC (CE η) b := by
  obtain ⟨rt, pw, t1, iws, t2, jws, μ0, u0, i0, j0, a0, sg0, w0, jx, hea, hei, -, hbe, hni, -, hb, hlo0, hjx,
    hbb⟩ := hrd
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨c, hsto, hat⟩ :=
        lane_slotW hi htv ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩ hea hei hbe hni hb hlo0
      exact .inl ⟨_, _, jx, lanes_comp hsto hat, hjx, hbb⟩

#print axioms ldlw_rdC


theorem offs_01 {b0 b : Address} {j : Nat} (hj : j < nWords [Acc.two]) (hb : b = offs b0 (0 + j)) :
    b = b0 ∨ b = b0.next := by
  have h2 : j < 2 := by simpa [nWords, Acc.size] using hj
  subst hb
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact .inl (offs_zero b0)
  · exact .inr (by cases b0; simp [offs, WeakMem.Address.next])

theorem pair_rdC {E : TEnv} {b : Address} (h : WordUnit E b ∨ EPairUnit E b) : RdC E b :=
  h.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr (.inl h)))

/-- **The op-level typed classification.** -/
theorem op_rdC {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {op : Op} {b : Address}
    (hop : OpT p cx x op c') (hsc : OpScope cx op ∨ OpScopeR th.σs cx op)
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hrd : RdOp g th.env (stOf mem pairs th) op b) :
    RdC (CE η) b := by
  cases op
  case load acq a =>
    rcases hsc with h | h
    · exact load_rdC hop h hi hE htv hrd
    · simp only [OpScopeR] at h
  case ldp acq a n0 n1 =>
    obtain ⟨rt, pw, b0, j, hea, -, hb0, hj, hb⟩ := hrd
    rcases hsc with h | h
    · cases hop with
      | ldp hp _ _ => exact pair_rdC (pair_rd hi.2.1 hp (h _ hp) hea hb0 (offs_01 hj hb))
    · simp only [OpScopeR] at h
  case fetch o acq rel a v =>
    obtain ⟨rt, pw, tv, nw, hea, -, hb⟩ := hrd
    rcases hsc with h | h
    · exact rmw_rdC (TermOwnCR5.fetch_cls2 hop h hi hE htv hm hea hb)
    · simp only [OpScopeR] at h
  case loadAt bb i => exact loadAt_rdC hop hi hE htv hrd
  case loadAtF bb i q => exact loadAtF_rdC hop hi hE htv hrd
  case ldl bb i => exact ldl_rdC hop hi htv hrd
  case ldlw bb wi jl => exact ldlw_rdC hop hi htv hrd
  case inl τ a =>
    cases hop with
    | inl _ hu _ => exact .inr (.inr (.inr (box_none hE hi htv hm hu hrd)))
  case inr τ a =>
    cases hop with
    | inr _ hu _ => exact .inr (.inr (.inr (box_none hE hi htv hm hu hrd)))
  case new a =>
    refine .inr (.inr (.inr ?_))
    have hf : b.label = _ := hrd
    rw [hf]; exact (hm.2.2.2.1.1 _ (Nat.le_refl _)).1
  case newBuf n τ =>
    refine .inr (.inr (.inr ?_))
    have hf : b.label = _ := hrd
    rw [hf]; exact (hm.2.2.2.1.1 _ (Nat.le_refl _)).1
  all_goals simp only [RdOp] at hrd

#print axioms op_rdC

/-- **The step-level typed classification.** -/
theorem tstep_rdC {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv}
    {K : TEnv → List Word → Prop} {cx : Cx} {r : Memory × List Ts × TTh} {b : Address}
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx) (hi : FInv ρ η th.σs K cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (h : r ∈ tstep g mem pairs th)
    (h1 : th.vs.coh b < r.2.2.vs.coh b) (h2 : r.2.2.vs.coh b < mem.size) (h3 : r.2.2.vs.coh b ∉ th.promises) :
    RdC (CE η) b := by
  rcases tstep_rd h (MemInv_promLt hm) h1 h2 h3 with ⟨x, op, e, hterm, hrd⟩ | ⟨a, x, e1, y, e2, hterm, hB⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t, pw, hterm, hea, hb⟩ |
      ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, t, pw, b0, hterm, hea, hb0, hb⟩
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ => exact op_rdC hop hsc hi hE htv hm hrd
  · rw [hterm] at hT
    cases hT with
    | case hu _ _ _ _ => exact .inr (.inr (.inr (box_none hE hi htv hm hu hB)))
  · rw [hterm] at hT hsc
    rcases hsc with hs | hs
    · exact rmw_rdC (TermOwnCR5.cas_cls2 hT hs hi hE htv hm hea hb)
    · simp only [StepScopeR] at hs
  · rw [hterm] at hT hsc
    obtain ⟨tw, hp⟩ : ∃ tw, cx.peek w = .ok tw := by cases hT <;> exact ⟨_, by assumption⟩
    rcases hsc with hs | hs
    · exact pair_rdC (pair_rd hi.2.1 hp (hs _ hp) hea hb0 hb)
    · simp only [StepScopeR] at hs

#print axioms tstep_rdC

/-- **ReadCls, step form.** -/
theorem tstep_readCls {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {r : Memory × List Ts × TTh} {b : Address} {cl : Cell}
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx) (hi : FInv ρ η th.σs K cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (h : r ∈ tstep g mem pairs th)
    (hsto : (CE η).sto b.label = some cl) (ho : cl.owner = some η.tid) (hclo : Clo cl.ty)
    (hmg : mg cl.ty = true) (hnw : ¬ WordUnit (CE η) b) (hne : ¬ EPairUnit (CE η) b)
    (h1 : th.vs.coh b < r.2.2.vs.coh b) (h2 : r.2.2.vs.coh b < mem.size) (h3 : r.2.2.vs.coh b ∉ th.promises) :
    ∃ q U us, TermPiece.Piece cl.ty q U ∧ accs U = some us ∧ q ≤ b.offset ∧ b.offset < q + nWords us ∧
      Ty.affine U = false := by
  rcases tstep_rdC hE hT htv hi hm hsc h h1 h2 h3 with ⟨b0, us, j, hca, hj, hb⟩ | hw | hp | hn
  · obtain ⟨vals, hc, -, -⟩ := hm.2.1 b.label cl hsto ho
    exact readAt_goal hc hclo hmg hsto hca hj hb
  · exact absurd hw hnw
  · exact absurd hp hne
  · rw [hsto] at hn; cases hn

#print axioms tstep_readCls

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- `ReadClsF` with the epoch-pair exclusion (`¬ EPairUnit`, supplied from `promNoTwo`). -/
def ReadClsFE (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    PromAbove (stOf r.1 r.2.1 r.2.2) →
    ∀ (b : Address) (cl : Cell), (CE η).sto b.label = some cl → cl.owner = some i →
      (CE η).pfr b.label ≠ none → ¬ WordUnit (CE η) b → ¬ EPairUnit (CE η) b →
      th.vs.coh b < r.2.2.vs.coh b → r.2.2.vs.coh b < c.mem.size → r.2.2.vs.coh b ∉ th.promises →
      ∃ q U us, TermPiece.Piece cl.ty q U ∧ accs U = some us ∧ q ≤ b.offset ∧ b.offset < q + nWords us ∧
        Ty.affine U = false

/-- **`ReadClsFE` holds** (from the scope obligation). -/
theorem tctx_readCls (hsc : StepScopeF p k arch Sp Init MintOK c0) : ReadClsFE p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y _ b cl hsto ho _ hnw hne h1 h2 h3
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hE2, hT2, htv2, hi2, hsum2⟩ := hRE0
  have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
    ⟨hce2, congrArg (fun E => E.tid) hce2, hE2, hT2, htv2, hi2, hsum2.1⟩
  have hs0 := hsc X Y2
  have hm : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hm0
  have hFi : FInv ρ2 η2 th.σs (Resume p th.stack) cx2 th.env :=
    FInvR_FInv (htv2.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs2 E rd ws R h) hi2
  have hst : ∀ l, (CE η2).sto l = (CE η).sto l := fun l => by rw [Y.1, hce2]; rfl
  have hsG : Eg.sto b.label = some cl := cutSto_sub (by rw [Y.1] at hsto; exact hsto)
  have ho2 : cl.owner = some η2.tid := by rw [Y2.2.1]; exact ho
  exact tstep_readCls hE2 hT2.1 htv2 hFi hm hs0 X.hr (by rw [hst]; exact hsto) ho2 (X.inv.clo _ _ hsG)
    (X.inv.cmg _ _ hsG) (fun hw => hnw ((WordUnit_congr (hst _)).1 hw))
    (fun hp => hne ((EPairUnit_congr (hst _)).1 hp)) h1 h2 h3

#print axioms tctx_readCls

end


end TermReadCls
