import WeakCore.ELayer
import WeakCore.WLayer
set_option autoImplicit false
set_option maxErrors 100000
/-! (δ1) Generated: the internal RetPw-free ♭ layer N (ResumeBN/ThInvEBN/…).
Internal only: appears in no exit statement. PwEqN := True replaces the pubWords link. -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
def PwEqN (_t _u : Ty) (_ws : List Word) : Prop := True
def RetPwN (σs : List Ty) (stack : List Frame) (ret : Ty) : Prop :=
  ∀ (f : Frame) (rest : List Frame), stack = f :: rest → ∀ ws, PwEqN f.ty (close σs ret) ws
theorem retPwN_true {σs : List Ty} {st : List Frame} {r : Ty} : RetPwN σs st r := fun _ _ _ _ => trivial
theorem retPwN_skel {σs σs2 : List Ty} {st : List Frame} {r r2 : Ty} (_hS : PwSkel) (_h : RetPwN σs st r)
    (_hk : skel (close σs2 r2) = skel (close σs r)) : RetPwN σs2 st r2 := retPwN_true
theorem retPwN_eq {σs : List Ty} {st : List Frame} {r r2 : Ty} (_h : RetPwN σs st r) (_e : r2 = r) :
    RetPwN σs st r2 := retPwN_true
end TermSound.Flat

namespace TermStep.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
/-- (ε) the counts at an existing label do not rise, unless the pre-term is a `bufInit` there. -/
def CntX (th0 : TTh) (E E' : TEnv) : Prop :=
  ∀ l, E.sto l ≠ none → ¬ TermOwnX2.Flat.BufInitL th0 l → E'.ini l ≤ E.ini l ∧ E'.rini l ≤ E.rini l
/-- (ε) the N footprint: `EFootPB` plus `CntX`. -/
abbrev EFootCN (g : G) (th0 : TTh) (E E' : TEnv) (s s' : St) : Prop := EFootPB g E E' s s' ∧ CntX th0 E E'
theorem cntX_refl {th0 : TTh} {E : TEnv} : CntX th0 E E := fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
theorem cntX_of_eq {th0 : TTh} {E E' : TEnv} (hi : ∀ l, E'.ini l = E.ini l) (hr : ∀ l, E'.rini l = E.rini l) :
    CntX th0 E E' := fun l _ _ => ⟨Nat.le_of_eq (hi l), Nat.le_of_eq (hr l)⟩
theorem cnE {g : G} {th0 : TTh} {E E' : TEnv} {s s' : St} (h : EFootPB g E E' s s')
    (hi : ∀ l, E'.ini l = E.ini l := by intro _; rfl) (hr : ∀ l, E'.rini l = E.rini l := by intro _; rfl) :
    EFootCN g th0 E E' s s' := ⟨h, cntX_of_eq hi hr⟩
theorem cnF {g : G} {th0 : TTh} {E E' : TEnv} {s s' : St} (hc : CntX th0 E E') (h : EFootPB g E E' s s') :
    EFootCN g th0 E E' s s' := ⟨h, hc⟩
theorem cnC {g : G} {th0 : TTh} {E E' : TEnv} {s1 s s' : St} (h : EFootCN g th0 E E' s1 s')
    (hn : s1.nalloc = s.nalloc) (hv : s1.vs.vWr = s.vs.vWr) (hz : s1.mem.size = s.mem.size)
    (hpr : s1.promises = s.promises) (hme : s1.mem = s.mem) : EFootCN g th0 E E' s s' :=
  ⟨EFoot_congrB h.1 hn hv hz hpr hme, h.2⟩
end TermStep.Flat

-- PORTB TermSound.lean:9231 Resume
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
def ResumeBN (lb n i : Nat) (p : Prog) : List Frame → TEnv → List Word → Prop
  | [], _, _ => True
  | f :: rest, E, ws => ∃ ρ η c, CE η = E ∧ EnvOKB p η ∧ Typed p c f.body ∧ TvOK c ∧
      FInvB lb n i ρ η f.σs (ResumeBN lb n i p rest) c ((f.x, f.ty, ws) :: f.env) ∧
      (∀ (f' : Frame) (rest' : List Frame), rest = f' :: rest' → ∀ ws,
        PwEqN f'.ty (close f.σs c.ret) ws) ∧
      DyFr p annNew (progTgts p) η f.σs f.body
end
end TermSound.Flat

-- PORTB TermSound.lean:11299 ThInvE
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
def ThInvEBN (lb n i : Nat) (p : Prog) (E : TEnv) (th : TTh) : Prop :=
  ∃ ρ η cx, CE η = E ∧ EnvOKB p η ∧ Typed p cx th.term ∧ TvOK cx ∧
    FInvB lb n i ρ η th.σs (ResumeBN lb n i p th.stack) cx th.env ∧ RetPwN th.σs th.stack cx.ret ∧
    DyFr p annNew (progTgts p) η th.σs th.term
end
end TermSound.Flat

-- PORTB TermSound.lean:11498 tstep_pure
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_pureBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {op : Op} {e : Expr}
    (hterm : th.term = .let_ x op e) (hA : PureOp op) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      have hne := pure_progressB g (stOf mem pairs th) hop hA hi
      have key : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) op).map
          fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
        cases op <;> simp only [PureOp] at hA <;> simp [tstep, hterm]
      rw [key]
      refine ⟨by simpa using hne, ?_⟩
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
      obtain ⟨ρ', h'⟩ := pure_presB hop hA hi hm (fun k => (hE.2.1 k).1) hE.2.1
      exact ⟨ρ', η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, h', retPwN_skel hPS hpw (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11521 tstep_ifeq
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_ifeqBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a b : At} {yes no : Expr}
    (hterm : th.term = .ifeq a b yes no) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  rcases ifeq_stepB hT hi htv with ⟨ra, wa, rb, wb, n, m, hea, heb, hwa, hwb, hy, hn⟩ |
      ⟨ra, wa, rb, wb, la, lb, hea, heb, hwa, hwb, hy, hn⟩
  rotate_left
  · simp only [tstep, hterm, hea, heb, hwa, hwb]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    by_cases h : la = lb
    · exact ⟨ρ, η, cx, rfl, hE, by simpa [h] using hy, htv, hi, retPwN_skel hPS hpw (skel_subst_eq rfl th.σs 0 0 0), hDy.iteW (fun _ => by rw [hterm]; rfl) rfl⟩
    · exact ⟨ρ, η, cx, rfl, hE, by simpa [h] using hn, htv, hi, retPwN_skel hPS hpw (skel_subst_eq rfl th.σs 0 0 0), hDy.iteW (fun _ => by rw [hterm]; rfl) rfl⟩
  simp only [tstep, hterm, hea, heb, hwa, hwb]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  by_cases h : n = m
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := hy h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.iteW (fun _ => by rw [hterm]; rfl) rfl⟩
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := hn h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.iteW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11550 tstep_parity
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_parityBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {k : String} {ev₀ od : Expr}
    (hterm : th.term = .parity a k ev₀ od) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨r, w, n, hea, hw, he, ho⟩ := parity_stepB hT hi htv
  simp only [tstep, hterm, hea, hw]
  refine ⟨by simp, ?_⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  by_cases h : n % 2 = 0
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := he h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.iteW (fun _ => by rw [hterm]; rfl) rfl⟩
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := ho h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.iteW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11569 tstep_split
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_splitBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e : Expr}
    (hterm : th.term = .split a x y e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨ra, rb, ws, us, hea, hus, c, hc, hvc, hk, hf⟩ := split_stepB hT hi htv
  simp only [tstep, hterm, hea, hus]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa using hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11584 tstep_unpack
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_unpackBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {i x : String} {e : Expr}
    (hterm : th.term = .unpack a i x e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨rb, ws, hea, ρ', c, hc, hvc, hk, hf⟩ := unpack_stepB hT hi htv
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ', η, c, rfl, hE, hc, hvc, by simpa using hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11599 tstep_unpackT
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_unpackTBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {α x : String} {e : Expr}
    (hterm : th.term = .unpackT a α x e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨κ, rb, ws, hea, s, hs, c, hc, hvc, hk, hf⟩ := unpackT_stepB hT hi hE.2.1 htv
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ, η.consCB s, c, rfl, ⟨hE.1, Coh_consCB hE.2.1 hs, CohR_consCB hE.2.2 hs⟩, hc, hvc, by simpa using hf, retPwN_skel hPS hpw hk, by rw [hterm] at hDy; exact hDy.unpackT s⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11614 tstep_ifnull
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_ifnullBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .ifnull a e₁ y e₂) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨μ, u, w, hea, h⟩ := ifnull_stepB hT hi htv
  rcases h with ⟨hw, c, hc, hvc, hk, hf⟩ | ⟨ad, hw, c, hc, hvc, hk, hf⟩
  · simp only [tstep, hterm, hea, hw]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa using hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩
  · simp only [tstep, hterm, hea, hw]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa using hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11636 tstep_inl
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_inlBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum t τ)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | inl _ hu hb =>
          obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
          have hS : (Ty.sum rt (close th.σs τ)).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum _ τ)) (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, hvr, hlay⟩ := inl_valueB hv hl hS
          have hta := (tier_sum hS).1
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 hvr hlay, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11667 tstep_inr
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_inrBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum τ t)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | inr _ hu hb =>
          obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
          have hS : (Ty.sum (close th.σs τ) rt).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum τ _)) (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, hvr, hlay⟩ := inr_valueB hv hl hS
          have hta := (tier_sum hS).2
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 hvr hlay, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11698 tstep_case
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_caseBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs t).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨ra, rb, ws, j, p', hea, hS, has, hA, hB⟩ := case_stepB hT hi hnb htv
  obtain ⟨hta, htb⟩ := tier_sum hS
  by_cases hj : j < (armsOf ra).length
  · obtain ⟨q, hq, c, hc, hvc, hk, hf⟩ := hA hj
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_true, injM_nb hta, hq, List.map_cons, List.map_nil,
      List.append_nil]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa [withS] using hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩
  · obtain ⟨q, hq, c, hc, hvc, hk, hf⟩ := hB (by omega)
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_false, injM_nb htb, hq, List.map_cons, List.map_nil,
      List.append_nil]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa [withS] using hf, retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:13759 tstep_ret
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_retBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At}
    (hterm : th.term = .ret a) (hst : th.stack ≠ []) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (hSupI : SupI g.lbase g.n g.i η) (htv : TvOK cx) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | ret hu _ hsub =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
      have hK := hi1.2.2.1 η (Ext_reflB hE.2.1 hE.2.2) hSupI ws (by rw [← hs]; exact VR_subB (bkG := False) hi1.1 hsub _ _ hv) hl'
      cases hstk : th.stack with
      | nil => exact absurd hstk hst
      | cons f rest =>
          rw [hstk] at hK
          obtain ⟨ρ', η', c, hCE, hE', hc, hvc, hf, hpwF, hDF⟩ := hK
          simp only [tstep, hterm, hstk, hea]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ', η', c, hCE, hE', hc, hvc, hf, hpwF, hDF⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:14776 tstep_call
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_callBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.call f is a ts) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hZ : ZeroCloseP)
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hpw : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      cases hop with
      | @call _ _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub hb =>
          obtain ⟨us, hlen, rfl, rfl⟩ := instantiate_ok hinst
          have hd := find_ok hfind
          have hDT := hP d (List.mem_of_find?_eq_some hd)
          have hRI := ProgRetIall.ret d (List.mem_of_find?_eq_some hd)
          obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
          obtain ⟨hi1, rt0, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
          have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
          have Er := skel_call th.σs ts us d.retTy (hlen ▸ TvB_skel _ _ _ hwr)
          have Lr := lyt_call th.σs ts us d.retTy (hlen ▸ TvB_of_wf _ _ _ hwr)
          obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
          simp only [tstep, hterm, callFrame, enter, hp, hd, hea, Option.bind, bind, pure,
            Option.map_some, ol, Option.toList_some]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨vinsL 0 (us.map (ev ρ)) ρ, subEB ρ η ts.reverse, declCx d, rfl, ⟨hE.1, Coh_subEB hE.2.1, CohR_subEB hE.2.1 hE.2.2⟩, hbody, declCx_TvOK hDT hRI,
            ⟨Sat_nil _, ?_, ?_, ?_, ?_⟩,
            fun _ _ _ _ => trivial, by rw [hterm] at hDy; obtain ⟨S, H, hS, hin, hσ, hX⟩ := hDy.callEdge; exact dyFr_enter (progDy_of_checked (ProgRetIall.checked (p := p))) hS hin hσ hX (fun k => (hE.2.1 k).1) hd (ts_tb_of_inst hinst hi.2.2.2.2.1)⟩
          · intro y en hen
            simp only [declCx, List.find?_cons, List.find?_nil] at hen
            split at hen
            · rename_i hy
              simp only [Option.some.injEq] at hen; subst hen
              have hy' : d.arg = y := by simpa using hy
              subst hy'
              refine ⟨_, ws, by simp [lookupE], ?_, Lay_move hl' Ea⟩
              rw [← shp_of_skel Ea, ← hs]
              exact (VR_callB ts us η ρ d.argTy _ ws hE.2.1).1 (VR_subB (bkG := False) hi1.1 hsub _ _ hv)
            · simp at hen
          · intro η' hx hS ws' hv' hl2
            obtain ⟨h2, hC⟩ := Ext_backB (η₁ := subEB ρ η ts.reverse) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
            have hv'' := (VR_cohB (Coh_subEB h2.1) hx.1 hx.2.1.symm hC _ _ _ _).2 hv'
            refine ⟨ρ, η.withStoB η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini, c', hC, ⟨hE.1, h2.1, h2.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
              bind_FInvB hb (FInv_extB hE.2.1 h2 hi1) ((VR_callB ts us _ ρ d.retTy _ ws' h2.1).2 hv'') ?_, fun f rest h ws => by rw [bind_ret hb, use_ret hu]; exact hpw f rest h ws, by rw [hterm] at hDy; exact hDy.let_.wit rfl⟩
            exact ⟨hl2.1, (eskel_of_skel Er).symm, hl2.2.2.1, hl2.2.2.2.1, (elyt_of_lyt Lr).symm⟩
          · exact WitL_call hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) (instantiate_ts hinst)
          · exact ⟨by simp [declCx, hlen], KindsOK_call hZ hi.2.2.2.2.2.1 hi.2.2.2.2.1 hinst,
              WitAF_subE hi.2.2.2.2.2.2.1 (instantiate_arrFree hinst)
                (fun σ h => (hrt σ (List.mem_reverse.1 h)).2) (fun k => (hE.2.1 k).1)
                (fun σ h => mg_of_wf σ (instantiate_ts hinst σ (List.mem_reverse.1 h)).2),
              WitSh_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.1 hinst,
              WitC_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.1 hinst,
              WitN_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.2.1 hinst,
              WitR_call hi.2.2.2.2.2.2.2.2.2.2 hinst (fun σ h => (hrt σ h).1)⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:14839 tstep_tail
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_tailBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {f : String} {is : List String} {a : At} {ts : List Ty}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .tail f is a ts) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hZ : ZeroCloseP)
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | @tail _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub hsubr =>
      obtain ⟨us, hlen, rfl, rfl⟩ := instantiate_ok hinst
      have hd := find_ok hfind
      have hDT := hP d (List.mem_of_find?_eq_some hd)
      have hRI := ProgRetIall.ret d (List.mem_of_find?_eq_some hd)
      obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
      obtain ⟨hi1, rt0, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
      have Er := skel_call th.σs ts us d.retTy (hlen ▸ TvB_skel _ _ _ hwr)
      have Lr := lyt_call th.σs ts us d.retTy (hlen ▸ TvB_of_wf _ _ _ hwr)
      obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
      simp only [tstep, hterm, enter, hp, hd, hea, Option.bind, bind, pure,
        Option.map_some, ol, Option.toList_some]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨vinsL 0 (us.map (ev ρ)) ρ, subEB ρ η ts.reverse, declCx d, rfl, ⟨hE.1, Coh_subEB hE.2.1, CohR_subEB hE.2.1 hE.2.2⟩, hbody, declCx_TvOK hDT hRI,
            ⟨Sat_nil _, ?_, ?_, ?_, ?_⟩,
            fun _ _ _ _ => trivial, by rw [hterm] at hDy; obtain ⟨S, H, hS, hin, hσ, hX⟩ := hDy.tailEdge; exact dyFr_enter (progDy_of_checked (ProgRetIall.checked (p := p))) hS hin hσ hX (fun k => (hE.2.1 k).1) hd (ts_tb_of_inst hinst hi.2.2.2.2.1)⟩
      · intro y en hen
        simp only [declCx, List.find?_cons, List.find?_nil] at hen
        split at hen
        · rename_i hy
          simp only [Option.some.injEq] at hen; subst hen
          have hy' : d.arg = y := by simpa using hy
          subst hy'
          refine ⟨_, ws, by simp [lookupE], ?_, Lay_move hl' Ea⟩
          rw [← shp_of_skel Ea, ← hs]
          exact (VR_callB ts us η ρ d.argTy _ ws hE.2.1).1 (VR_subB (bkG := False) hi1.1 hsub _ _ hv)
        · simp at hen
      · intro η' hx hS ws' hv' hl2
        obtain ⟨h2, hC⟩ := Ext_backB (η₁ := subEB ρ η ts.reverse) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
        have hv'' := (VR_cohB (Coh_subEB h2.1) hx.1 hx.2.1.symm hC _ _ _ _).2 hv'
        have hlr : Lay th.σs (substTs ts.reverse 0 0 (instT us 0 d.retTy)) (close (ts.map (close th.σs)).reverse d.retTy) ws' :=
          ⟨hl2.1, (eskel_of_skel Er).symm, hl2.2.2.1, hl2.2.2.2.1, (elyt_of_lyt Lr).symm⟩
        obtain ⟨hs2, hl3⟩ := Lay_canon hsubr hlr
        rw [← hC]
        refine hi1.2.2.1 _ h2 (SupI_CE_eq hC hS) ws' ?_ hl3
        rw [← hs2]
        exact VR_subB (bkG := False) hi1.1 hsubr _ _ ((VR_callB ts us _ ρ d.retTy _ ws' h2.1).2 hv'')
      · exact WitL_call hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) (instantiate_ts hinst)
      · exact ⟨by simp [declCx, hlen], KindsOK_call hZ hi.2.2.2.2.2.1 hi.2.2.2.2.1 hinst,
              WitAF_subE hi.2.2.2.2.2.2.1 (instantiate_arrFree hinst)
                (fun σ h => (hrt σ (List.mem_reverse.1 h)).2) (fun k => (hE.2.1 k).1)
                (fun σ h => mg_of_wf σ (instantiate_ts hinst σ (List.mem_reverse.1 h)).2),
              WitSh_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.1 hinst,
              WitC_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.1 hinst,
              WitN_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.2.1 hinst,
              WitR_call hi.2.2.2.2.2.2.2.2.2.2 hinst (fun σ h => (hrt σ h).1)⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:14998 tstep_fnptr
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_fnptrBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x f : String} {e : Expr}
    (hp : g.p = p) (hP : ProgT p)
    (hterm : th.term = .let_ x (.fnptr f) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | fnptr hfind htp hidx hb =>
          rename_i d
          have hd := find_ok hfind
          obtain ⟨i, hix, hpi⟩ := findIdx_of_find hd
          obtain ⟨hwa, hwr, -, -, -⟩ := hP d (List.mem_of_find?_eq_some hd)
          have hwa' : d.argTy.wf 0 0 = true := by simpa [htp, hidx] using hwa
          have hwr' : d.retTy.wf 0 0 = true := by simpa [htp, hidx] using hwr
          have hn : d.name = f := by simpa using List.find?_some hd
          have hvr : ∀ kd, (VRF False) ρ η (.code d.argTy d.retTy kd) (shp (.code d.argTy d.retTy kd)) [cst (.num i)] := by
            intro kd
            simp only [VRF, VRb2]
            refine ⟨i, d, rfl, by rw [hE.1]; exact hpi, by rw [hE.1, hn]; exact hd, htp, hidx,
              cl_wf _ hwa', cl_wf _ hwr'⟩
          simp only [tstep, hterm, evalOp, hp, hix, hd, List.map_cons, List.map_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ, η, c', rfl, hE, he, htv', by (have h := bind_FInvB hb hi (hvr _) (Lay_code th.σs hwa' hwr' _); (try simp only [withS] at h); (try simp only [withS]); revert h; cases d.kind <;> exact id), retPwN_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:15036 tstep_callc
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem tstep_callcBN {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {f a : At} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.callc f a) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hpw : RetPwN th.σs th.stack cx.ret) (hSig : PwSig) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      cases hop with
      | @callc c₁ _ _ _ _ tf σ τ t htf hc hu _ hsub hb =>
          obtain ⟨σ', τ', kf, rfl⟩ : ∃ a b kf, tf = .code a b kf := by cases tf <;> simp_all [codeOf]
          simp only [codeOf, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨h1, h2⟩ := hc
          subst σ' τ'
          obtain ⟨rtf, wsf, hef, hvf, hlf⟩ := peek_VRB (bkG := False) hi.2.1 htf
          simp only [VRF, VRb2] at hvf
          obtain ⟨i, D, hwv, hpi, hfd, htp, hidx, lσ, lτ⟩ := hvf
          obtain ⟨w, rfl, hw⟩ := map_singleton hwv
          rw [hE.1] at hpi hfd
          have hDT := hP D (List.mem_of_find?_eq_some hfd)
          have hRI := ProgRetIall.ret D (List.mem_of_find?_eq_some hfd)
          obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
          have hwa' : D.argTy.wf 0 0 = true := by simpa [htp, hidx] using hwa
          have hwr' : D.retTy.wf 0 0 = true := by simpa [htp, hidx] using hwr
          
          
          have hc : etok (skel rtf) = .code (etok (skel (close th.σs σ))) (etok (skel (close th.σs τ))) kf := hlf.2.1
          obtain ⟨ra, rr, rfl, hsa, hsr⟩ := eskel_eq_code hc
          
          
          
          have htbf := peek_tb htv htf
          simp only [tb, Bool.and_eq_true] at htbf
          have hoσ : cx.opaqueOK σ = true :=
            sub_opaqueOK hsub (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
          have hoτ : cx.opaqueOK τ = true := by
            have h := bind_opaqueOK hb; unfold Cx.opaqueOK at h ⊢; rwa [(use_opq hu).1] at h
          have hD : ∀ v : Ty, v.wf 0 0 = true → sig (clD v) = sig (close [] v) := fun v hv =>
            (sig_close_cl [] (fun _ => 0) (fun _ => .void) v 0 0 (fun k hk =>
              absurd (lt_of_guardT (tb_of_wf v hv) (Nat.le_refl 0) k (by simpa using hk))
                (Nat.not_lt_zero _))).symm
          have Ea : sig (close th.σs σ) = sig (close [] D.argTy) := by
            rw [sig_WitL hi.2.2.2.1 ρ hoσ (lt_of_guardT htbf.1 hi.2.2.2.2.1), lσ, hD _ hwa']
          have Er : sig rr = sig (close [] D.retTy) := by
            have e : sig rr = sig (close th.σs τ) := sig_of_eskel hsr
            rw [e, sig_WitL hi.2.2.2.1 ρ hoτ (lt_of_guardT htbf.2 hi.2.2.2.2.1), lτ, hD _ hwr']
          obtain ⟨hi1, rt0, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
          obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
          simp only [tstep, hterm, hef, hw, hp, hpi, callFrame, enter, hfd, hea, retOf, Option.bind, bind, pure,
            Option.map_some, ol, Option.toList_some, List.map_nil, List.reverse_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨fun _ => 0, CE η, declCx D, rfl, ⟨hE.1, Coh_CEB η, CohR_CEB η⟩, hbody, declCx_TvOK hDT hRI, ⟨Sat_nil _, ?_, ?_, ?_, ?_⟩,
            fun _ _ _ _ => trivial, dyFr_enter_nil (progDy_of_checked (ProgRetIall.checked (p := p))) (List.mem_of_find?_eq_some hfd)⟩
          · intro y en hen
            simp only [declCx, List.find?_cons, List.find?_nil] at hen
            split at hen
            · rename_i hy
              simp only [Option.some.injEq] at hen; subst hen
              have hy' : D.arg = y := by simpa using hy
              subst hy'
              refine ⟨_, ws, by simp [lookupE], ?_, Lay_move_sig hl' Ea⟩
              rw [← shp_of_sig Ea, ← hs]
              exact (VR_codeB hE.2.1 lσ _ _).1 (VR_subB (bkG := False) hi1.1 hsub _ _ hv)
            · simp at hen
          · intro η' hx hS ws' hv' hl2
            obtain ⟨h2, hC⟩ := Ext_backB (η₁ := CE η) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
            have hv'' : (VRF False) (fun _ => 0) (CE (η.withStoB η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini)) D.retTy _ ws' :=
              (VR_cohB hx.1 (Coh_CEB (η.withStoB η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini)) hx.2.1 hC.symm _ _ _ _).1 hv'
            have hw2 : wc (close [] D.retTy) = wc rr := (wc_of_sig Er).symm
            refine ⟨ρ, η.withStoB η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini, c', hC, ⟨hE.1, h2.1, h2.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', bind_FInvB hb (FInv_extB hE.2.1 h2 hi1) ?_
              ⟨ShapeC_wc hw2 hl2.1, hsr, hw2 ▸ hl2.2.2.1, Valid_of_sig Er.symm hl2.2.2.2.1, by
                have hy := hlf.2.2.2.2
                simp only [close, substTs, lyt, etok, Ty.code.injEq] at hy
                exact hy.2.1⟩, fun f rest h ws => by rw [bind_ret hb, use_ret hu]; exact hpw f rest h ws, by rw [hterm] at hDy; exact hDy.let_.wit rfl⟩
            rw [shp_of_sig Er]; exact (VR_codeB h2.1 lτ _ _).2 hv''
          · exact ⟨fun k _ hk => by simp at hk, fun k σ h => by simp at h, fun k _ hk => by simp at hk⟩
          · exact ⟨by simp [declCx, htp], ⟨fun k hk => by simp [declCx, htp, KEnv.ask] at hk, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun _ h => by simp at h⟩, WitAF_CE η, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun k hk => by simp [declCx, htp, KEnv.ask] at hk, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun k hk => by simp [declCx, htp, KEnv.ask] at hk⟩
end
end TermSound.Flat

-- PORTB TermStep.lean:3111 ThInvMF
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
def ThInvMFBN (p : Prog) (g : G) (E : TEnv) (s : St) (th0 : TTh) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E', EFootCN g th0 E E' s (stOf mem pairs th) ∧ ThInvEBN g.lbase g.n g.i p E' th ∧ MemInvB g E' (stOf mem pairs th)
end
end TermStep.Flat

-- PORTB TermStep.lean:3116 ThInvMFP
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
def ThInvMFPBN (p : Prog) (g : G) (E : TEnv) (s : St) (th0 : TTh) (mem : Memory) (pairs : List Ts) (th : TTh) :
    Prop :=
  ∃ E', EFootCN g th0 E E' s (stOf mem pairs th) ∧ ThInvEBN g.lbase g.n g.i p E' th ∧ MemInvB g E' (stOf mem pairs th) ∧
    ∀ y a e rt ws ad, th0.term = .let_ y (.publish a) e → evalAt th0.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → E'.pfr ad.label ≠ none
end
end TermStep.Flat

-- PORTB TermStep.lean:5511 lift
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem liftBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    (hm : MemInvB g E (stOf mem pairs th))
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p E r.2.2)
    (hs : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g E (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  ⟨h.1, fun r hr => ⟨E, ⟨EFoot_reflB, cntX_refl⟩, h.2 r hr, MemInv_sameB hm (hs r hr)⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:17567 tstepM_loadCell
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_loadCellBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.ptr μ u)) (haf : affine cx.ke u = false) (hb : cx.bind x u = .ok c')
    (he : Typed p c' e) (htv' : TvOK c') (hRk : skel c'.ret = skel cx.ret)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel)
    (hV : ∀ (F : Prop) rt pw ad c, evalAt th.env a = some (rt, [pw]) → pw.val = .loc ad 0 → η.sto ad.label = some c →
      (ModeOKF F) η.tid η.pfr η.seen μ ad.label c [pw] → (ModeOKF F) η.tid η.pfr η.seen .pub ad.label c [pw]) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨ru, L, key, hne, hld, -⟩ := loadCell_stepB (g := g) (mem := mem) (pairs := pairs) hterm hpk haf hb hi hE htv hm hV
  rw [key]
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay', hm'⟩ := hld s' wsr hl (hpr0)
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay', retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:17588 tstepM_loadPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_loadPubBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  exact tstepM_loadCellBN (hDy := hDy) (hterm := hterm) (hpk := hpk) (haf := haf) (hb := hb) (he := he) (htv' := htv') (hRk := hRk) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS) (hV := fun _ _ _ _ _ _ _ _ h => h)
end
end TermStep.Flat

-- PORTB TermStep.lean:18282 tstepM_publish
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_publishBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : PubScope cx a)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      NoHold (CE η) (stOf mem pairs th) ad.label)
    (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFPBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, hsh, hb⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind x (.ptr .pub u) = .ok c' := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨hi1, lab, c, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, hl⟩ := ownPtr_invB hu hi
    have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
    simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh
    have hF := pubTyFactsB hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc hsh.1.1 hsh.1.2
      (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
    obtain ⟨hfoot, hx, hmi⟩ := pubCell_postB (Rd := η.rid) hE hm hsto hown (Nat.le_refl _) hF
      (hwin _ _ ⟨lab, 0⟩ hea hwsv) (hPb x a e _ _ ⟨lab, 0⟩ hterm hea hwsv)
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .ptr .pub ru, [pw]) :: th.env } (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hvr : (VRF False) ρ (pubEnvAtB η lab (stOf mem pairs th).vs.vWr η.rid) (.ptr .pub u) (shp (.ptr .pub ru)) [pw] := by
      simp only [VRF, VRb2]
      exact ⟨⟨lab, 0⟩, c, hwsv, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [pubEnvAtB, TEnv.withStoB, pubP], Or.inl (Or.inl rfl)⟩, hacc⟩
    exact ⟨_, cnE hfoot, ⟨ρ, _, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
        bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (Lay_ptr_remode hl rfl rfl),
        retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hmi,
      fun y a' e' rt' ws' ad' ht' hea' hws' => by
        rw [hterm] at ht'
        cases ht'
        rw [hea] at hea'
        cases hea'
        have h2 : [pw.val] = [.loc ad' 0] := hws'
        rw [hpw] at h2
        cases h2
        exact (pubEnvAtB_seen _ _ _ _).1⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, hsh, hb⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c' := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨hi1, μr, nr, ur, ψ, wsb, hea, hvb, hlay⟩ := ownBuf_invB (bkG := False) hu hi
    have hl := hlay .pub .pub rfl rfl
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc .pub (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, hir⟩ := hvb
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat, hFU, hmode, hini⟩
    · 
      have hvr : (VRF False) ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1,
          fun _ => Or.inr hir.1⟩
      refine ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hl, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fenceB hm,
        fun y a' e' rt' ws' ad' ht' hea' hws' => ?_⟩
      rw [hterm] at ht'
      cases ht'
      rw [hea] at hea'
      cases hea'
      rw [hnull] at hws'
      simp at hws'
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c.owner = some η.tid := hmode
      simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh
      have hF := pubTyFactsBufB hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat hsh.1.1 hsh.1.2
        (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      obtain ⟨hfoot, hx, hmi⟩ := pubCell_postB (Rd := η.rid) hE hm hsto hown (Nat.le_refl _) hF
        (hwin _ _ ad hea hws) (hPb x a e _ _ ad hterm hea hws)
      have hvr : (VRF False) ρ (pubEnvAtB η ad.label (stOf mem pairs th).vs.vWr η.rid)
          (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]
        exact ⟨Or.inr ⟨ad, c, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [pubEnvAtB, TEnv.withStoB, pubP], Or.inl (Or.inl rfl)⟩,
          (IniAt_mono (modeIni_le_ini _ _ _) hini)⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1,
            fun _ => Or.inr hir.1⟩
      exact ⟨_, cnE hfoot, ⟨ρ, _, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
          bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr hl, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hmi,
        fun y a' e' rt' ws' ad' ht' hea' hws' => by
          rw [hterm] at ht'
          cases ht'
          rw [hea] at hea'
          cases hea'
          rw [hws] at hws'
          cases hws'
          exact (pubEnvAtB_seen _ _ _ _).1⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:18571 tstepM_loadCellLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_loadCellLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.loc μ u))
    (haf : affine cx.ke u = false) (hb : cx.bind x u = .ok c')
    (he : Typed p c' e) (htv' : TvOK c') (hRk : skel c'.ret = skel cx.ret) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hμ : μ ≠ .own)
    (hV : ∀ (F : Prop) rt pw ad c, evalAt th.env a = some (rt, [pw]) → pw.val = .loc ad 0 → η.sto ad.label = some c →
      (ModeOKF F) η.tid η.pfr η.seen μ ad.label c [pw] → (ModeOKF F) η.tid η.pfr η.seen .pub ad.label c [pw]) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc μ u) = some (μ, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  replace hmode := hV _ _ pw ad c hea hpw hsto hmode
  rw [modeIni_ne_own hμ] at hini
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc μ u) = some (μ, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  by_cases hown : c.owner = some η.tid
  · 
    obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadIB (arch := g.arch) (pw := pw) (acq := acq)
      (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto hown hat hini hna
      (fun hir f hf hns => by
        simp only [ModeOKF, ModeOKb] at hmode
        obtain ⟨f0, hf0, hsf⟩ := hmode
        obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
        replace hsf := hsf.imp id (fun h => h.resolve_right (fun h1 => hir (h1.2.resolve_left id)))
        rcases hsf with hs | hs
        · exact absurd hs hns
        · exact hs pw (by simp)) hsku hsig
        (cell_lyt hl.2.2.2.2 rfl rfl).2
          (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨hvr, hlay', f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay', retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')⟩
  · 
    simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, hsf⟩ := hmode
    replace hsf := hsf.imp id (fun h => h.resolve_right (fun h1 => hown h1.1))
    have hfv : f ≤ pw.view := by
      rcases hsf with hs | hs
      · rcases hm.2.2.2.2.2.2.2.2.1.1 ad.label hs with ⟨c0, h1, h2⟩ | ⟨h1, -⟩
        · refine absurd ?_ hown
          have h1' : η.sto ad.label = some c0 := h1
          rw [hsto] at h1'
          rw [Option.some.inj h1']; exact h2
        · have h1' : η.sto ad.label = none := h1
          rw [hsto] at h1'; cases h1'
      · exact hs pw (by simp)
    have hlU : accs (cl ρ η.wit 0 0 u) ≠ none := by
      rcases AtOff_lay hat with h | ⟨N, e', h, -⟩
      · exact h
      · exact absurd h (hna N e')
    have hlr := pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl
    obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := Option.ne_none_iff_exists'.1 (by rw [hlr]; exact hlU)
    have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    obtain ⟨⟨r0, hr0⟩, hval, hsv⟩ := pubLoadAtB (arch := g.arch) (pw := pw) (acq := acq)
      hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.1 hsto hown hf hfv hat hini hna husU
    refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨q, hq, hle⟩ := hval (s', wsr) hl' (hpr0)
    have hrl : wsr.length = nWords us := (Reads_unit us 0 wsr (loadUnits_reads us 0 _ (s', wsr) hl' [] (fun _ _ h => by cases h))).1
    obtain ⟨f1, f2, f3, f4⟩ := loadUnits_frame us 0 _ (s', wsr) hl'
    obtain ⟨hvr0, hV0⟩ := ValOfB.env hq
    have hvr : (VRF False) ρ η u (shp ru) wsr := by
      rw [shp_of_sig hsig]
      exact (VR_closeB hE.2.1 ρ u [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 u)) wsr (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (VR_upB (bkG := False) _ _ q wsr hle hvr0)
    have hlay' : Lay th.σs u ru wsr :=
      ⟨fun us' h => by rw [hus] at h; cases h; exact hrl, hsku, by simp [wc, hus],
        Valid_of_sig hsig.symm (Valid_vals _ q wsr hle.vals hV0), (cell_lyt hl.2.2.2.2 rfl rfl).2⟩
    refine ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay', retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, ?_⟩
    refine MemInv_loadFB hm f1 f2 (fun l c1 hc1 ho1 o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ ?_)
      f3 f4 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')
      (fun l B hB o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ (fun he => by
        have h0 := (hm.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1
        have hl0 : l = ad.label := he
        rw [hl0] at h0; have h1 : η.sto ad.label = none := h0; rw [hsto] at h1; cases h1))
    intro hle'
    have hl'' : l = ad.label := hle'
    have h1 : η.sto l = some c1 := hc1
    rw [hl'', hsto] at h1
    exact hown (by rw [Option.some.inj h1]; exact ho1)
end
end TermStep.Flat

-- PORTB TermStep.lean:18694 tstepM_loadPubLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_loadPubLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  exact tstepM_loadCellLocBN (hDy := hDy) (hterm := hterm) (hpk := hpk) (haf := haf) (hb := hb) (he := he) (htv' := htv') (hRk := hRk) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS) (hμ := fun h => by cases h) (hV := fun _ _ _ _ _ _ _ _ h => h)
end
end TermStep.Flat

-- PORTB TermStep.lean:18786 tstepM_storeCell
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_storeCellBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {u : Ty} {tv : Ty} {c₁ : Cx} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.ptr μ u))
    (hu : cx.use v = .ok (tv, c₁)) (hsub : SubS c₁ tv u) (hb : c₁.bind x .unit = .ok c')
    (he : Typed p c' e) (htv' : TvOK c') (hRk : skel c'.ret = skel cx.ret) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel)
    (hV : ∀ (F : Prop) rt pw ad c, evalAt th.env a = some (rt, [pw]) → pw.val = .loc ad 0 → η.sto ad.label = some c →
      (ModeOKF F) η.tid η.pfr η.seen μ ad.label c [pw] → (ModeOKF F) η.tid η.pfr η.seen .pub ad.label c [pw]) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr μ u) = some (μ, u))
  obtain ⟨lab, c, pw, μr, ru, hea, hpw, hsto, hcty, hmode, hacc, -, hsku, hsig⟩ := ptr_viewB (bkG := False) hi hpk htv ho
  obtain ⟨f, hf, -⟩ := pubFrB hea hpw hsto (hV _ _ pw ⟨lab, 0⟩ c hea hpw hsto hmode)
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hlr : accs ru = accs c.ty := by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    cases h : accs ru with
    | none => rw [h] at hlr; exact absurd hlr.symm hacc
    | some us => exact ⟨us, rfl⟩
  have husc : accs c.ty = some us := by rw [← hlr, hus]
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  refine ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, ?_⟩
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeFB hm hsto hown husc hval hlen s' hs'
  · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
    exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
      (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs'
end
end TermStep.Flat

-- PORTB TermStep.lean:18832 tstepM_storePub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_storePubBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  exact tstepM_storeCellBN (hDy := hDy) (hterm := hterm) (hpk := hpk) (hu := hu) (hsub := hsub) (hb := hb) (he := he) (htv' := htv') (hRk := hRk) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS) (hV := fun _ _ _ _ _ _ _ _ h => h)
end
end TermStep.Flat

-- PORTB TermStep.lean:18953 tstepM_storeCellLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_storeCellLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {u : Ty} {tv : Ty} {c₁ : Cx} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    (hpk : cx.peek a = .ok (.loc μ u))
    (hu : cx.use v = .ok (tv, c₁)) (hsub : SubS c₁ tv u) (hb : c₁.bind x .unit = .ok c')
    (he : Typed p c' e) (htv' : TvOK c') (hRk : skel c'.ret = skel cx.ret) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hμ : μ ≠ .own)
    (hV : ∀ (F : Prop) rt pw ad c, evalAt th.env a = some (rt, [pw]) → pw.val = .loc ad 0 → η.sto ad.label = some c →
      (ModeOKF F) η.tid η.pfr η.seen μ ad.label c [pw] → (ModeOKF F) η.tid η.pfr η.seen .pub ad.label c [pw]) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc μ u) = some (μ, u))
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc μ u) = some (μ, u)) (Fd_noarr fun h => hwcu (by simp [wc, h])) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  replace hmode := hV _ _ pw ad c hea hpw hsto hmode
  rw [modeIni_ne_own hμ] at hini
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  have hlr := pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := hlr.symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  refine ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, ?_⟩
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeAtIB hm hsto hown hat hini hna hval hwUA hlen s' hs'
  · simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    exact MemInv_storePubAtB hm hsto hown hf hat hini hna hval husU hlen s' hs'
end
end TermStep.Flat

-- PORTB TermStep.lean:19020 tstepM_storePubLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem tstepM_storePubLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  exact tstepM_storeCellLocBN (hDy := hDy) (hterm := hterm) (hpk := hpk) (hu := hu) (hsub := hsub) (hb := hb) (he := he) (htv' := htv') (hRk := hRk) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS) (hμ := fun h => by cases h) (hV := fun _ _ _ _ _ _ _ _ h => h)
end
end TermStep.Flat

-- PORTB TermStep.lean:3155 ThInvMFA
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def ThInvMFABN (p : Prog) (g : G) (ρ : Nat → Nat) (η : TEnv) (th0 : TTh) (E : TEnv) (s : St) (mem : Memory)
    (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E', FreshArr g ρ η th0 E' (mem, pairs, th) ∧ EFootCN g th0 E E' s (stOf mem pairs th) ∧ ThInvEBN g.lbase g.n g.i p E' th ∧
    MemInvB g E' (stOf mem pairs th)
end
end TermStep.Flat

-- PORTB TermStep.lean:3167 ThInvMFS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def ThInvMFSBN (p : Prog) (g : G) (E : TEnv) (s : St) (th0 : TTh) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E', (∀ l, E'.sto l = E.sto l) ∧ EFootCN g th0 E E' s (stOf mem pairs th) ∧ ThInvEBN g.lbase g.n g.i p E' th ∧
    MemInvB g E' (stOf mem pairs th)
end
end TermStep.Flat

-- PORTB TermStep.lean:3176 ThInvMFS_congr
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ThInvMFSBN.toF {p : Prog} {g : G} {E : TEnv} {s : St} {th0 : TTh} {mem : Memory} {pairs : List Ts} {th : TTh}
    (h : ThInvMFSBN p g E s th0 mem pairs th) : ThInvMFBN p g E s th0 mem pairs th :=
  let ⟨E', _, h1, h2, h3⟩ := h
  ⟨E', h1, h2, h3⟩
theorem ThInvMFABN.toF {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {th0 : TTh} {E : TEnv} {s : St}
    {mem : Memory} {pairs : List Ts} {th : TTh} (h : ThInvMFABN p g ρ η th0 E s mem pairs th) :
    ThInvMFBN p g E s th0 mem pairs th :=
  let ⟨E', _, h1, h2, h3⟩ := h
  ⟨E', h1, h2, h3⟩
theorem ThInvMFPBN.toF {p : Prog} {g : G} {E : TEnv} {s : St} {th0 : TTh} {mem : Memory} {pairs : List Ts}
    {th : TTh} (h : ThInvMFPBN p g E s th0 mem pairs th) : ThInvMFBN p g E s th0 mem pairs th :=
  let ⟨E', h1, h2, h3, _⟩ := h
  ⟨E', h1, h2, h3⟩
end
end TermStep.Flat
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ThInvMFS_congrBN {p : Prog} {g : G} {E : TEnv} {s1 s : St} {th0 : TTh} {mem : Memory} {pairs : List Ts} {th : TTh}
    (h : ThInvMFSBN p g E s1 th0 mem pairs th) (hn : s1.nalloc = s.nalloc) (hv : s1.vs.vWr = s.vs.vWr)
    (hz : s1.mem.size = s.mem.size) (hpr : s1.promises = s.promises) (hme : s1.mem = s.mem) :
    ThInvMFSBN p g E s th0 mem pairs th :=
  let ⟨E', hs, hf, h1, h2⟩ := h
  ⟨E', hs, cnC hf hn hv hz hpr hme, h1, h2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:5519 liftS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem liftSBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    (hm : MemInvB g E (stOf mem pairs th))
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p E r.2.2)
    (hs : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSBN p g E (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  ⟨h.1, fun r hr => ⟨E, fun _ => rfl, ⟨EFoot_reflB, cntX_refl⟩, h.2 r hr, MemInv_sameB hm (hs r hr)⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:5700 tstepM_pure
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_pureBN {x : String} {op : Op} {e : Expr}
    (hterm : th.term = .let_ x op e) (hA : PureOp op) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_pureBN (hDy := hDy) hterm hA hP hT hi hE htv hRP hPS) (same_pure hterm hA)
end
end TermStep.Flat

-- PORTB TermStep.lean:5707 tstepM_ifeq
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ifeqBN {a b : At} {yes no : Expr}
    (hterm : th.term = .ifeq a b yes no) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_ifeqBN (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_ifeq hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5713 tstepM_parity
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_parityBN {a : At} {k : String} {ev₀ od : Expr}
    (hterm : th.term = .parity a k ev₀ od) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_parityBN (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_parity hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5719 tstepM_split
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_splitBN {a : At} {x y : String} {e : Expr}
    (hterm : th.term = .split a x y e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_splitBN (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_split hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5725 tstepM_unpack
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_unpackBN {a : At} {i x : String} {e : Expr}
    (hterm : th.term = .unpack a i x e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_unpackBN (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_unpack hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5731 tstepM_unpackT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_unpackTBN {a : At} {α x : String} {e : Expr}
    (hterm : th.term = .unpackT a α x e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_unpackTBN (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_unpackT hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5737 tstepM_ifnull
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ifnullBN {a : At} {y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .ifnull a e₁ y e₂) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_ifnullBN (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_ifnull hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5743 tstepM_inlS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inlSBN {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum t τ)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  refine liftSBN hm (tstep_inlBN (hDy := hDy) hterm hP hnb hT hi hE htv hRP hPS) (same_inl hterm fun t ws hea => ?_)
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
      cases hop with
      | inl _ hu _ =>
          obtain ⟨-, rt, ws', hea', -, hl⟩ := use_FInvB (bkG := False) hu hi
          rw [hea, Option.some.injEq, Prod.mk.injEq] at hea'
          obtain ⟨rfl, rfl⟩ := hea'
          rw [tier_of_eskel (u := close th.σs (.sum _ τ)) (by show Ty.sum (etok (skel t)) _ = _; rw [hl.2.1]; rfl)]
          exact hnb _ _ hu
end
end TermStep.Flat

-- PORTB TermStep.lean:5771 tstepM_inrS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inrSBN {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum τ t)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  refine liftSBN hm (tstep_inrBN (hDy := hDy) hterm hP hnb hT hi hE htv hRP hPS) (same_inr hterm fun t ws hea => ?_)
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
      cases hop with
      | inr _ hu _ =>
          obtain ⟨-, rt, ws', hea', -, hl⟩ := use_FInvB (bkG := False) hu hi
          rw [hea, Option.some.injEq, Prod.mk.injEq] at hea'
          obtain ⟨rfl, rfl⟩ := hea'
          rw [tier_of_eskel (u := close th.σs (.sum τ _)) (by show Ty.sum _ (etok (skel t)) = _; rw [hl.2.1]; rfl)]
          exact hnb _ _ hu
end
end TermStep.Flat

-- PORTB TermStep.lean:5799 tstepM_caseS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_caseSBN {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs t).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  refine liftSBN hm (tstep_caseBN (hDy := hDy) hterm hnb hT hi hE htv hRP hPS) ?_
  rw [hterm] at hT
  obtain ⟨ra, rb, ws, j, p', hea, hS, has, -, -⟩ := case_stepB hT hi hnb htv
  obtain ⟨hta, htb⟩ := tier_sum hS
  intro r hr
  by_cases hj : j < (armsOf ra).length
  · simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_true, injM_nb hta, List.append_nil, List.mem_map,
      Option.mem_toList, Option.map_eq_some_iff] at hr
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hr
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_false, injM_nb htb, List.append_nil, List.mem_map,
      Option.mem_toList, Option.map_eq_some_iff] at hr
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hr
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:5832 tstepM_ret
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_retBN {a : At}
    (hterm : th.term = .ret a) (hst : th.stack ≠ []) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hn : 0 < g.n) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_retBN hterm hst hT hi hE (supI_of_memInvB hm hn) htv) (same_ret hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5839 tstepM_call
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_callBN {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.call f is a ts) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_callBN (hDy := hDy) hp hP hterm hT hi hE htv KindSound.zero_close hrt hRP) (same_call hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5848 tstepM_tail
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_tailBN {f : String} {is : List String} {a : At} {ts : List Ty}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .tail f is a ts) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_tailBN (hDy := hDy) hp hP hterm hT hi hE htv KindSound.zero_close hrt hRP hPS hSub) (same_tail hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5857 tstepM_fnptr
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_fnptrBN {x f : String} {e : Expr}
    (hp : g.p = p) (hP : ProgT p)
    (hterm : th.term = .let_ x (.fnptr f) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_fnptrBN (hDy := hDy) hp hP hterm hT hi hE htv hRP hPS) (same_fnptr hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5865 tstepM_callc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_callcBN {x : String} {f a : At} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.callc f a) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hSig : PwSig) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_callcBN (hDy := hDy) hp hP hterm hT hi hE htv hRP hSig) (same_callc hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5899 tstepM_newA
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newABN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFABN p g ρ η th (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | new hu _ hb =>
  obtain ⟨tv, c₁, hu, hb⟩ : ∃ tv c₁, cx.use a = .ok (tv, c₁) ∧ c₁.bind x (.ptr .own tv) = .ok c' :=
    ⟨_, _, hu, hb⟩
  obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
  have ho : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 tv) := lay_closed hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl
  obtain ⟨us, hus⟩ : ∃ us, accs rt = some us := by
    cases h : accs rt with
    | none => exact absurd (by simp [wc, h]) hl.2.2.1
    | some us => exact ⟨us, rfl⟩
  have hlen : ws.length = nWords us := hl.1 us hus
  have hwcT : wc (cl ρ η.wit 0 0 tv) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvc : (VRF False) (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws := by
    rw [← shp_of_sig hsig]
    exact (VR_closeB hE.2.1 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := hm
  obtain ⟨hnone, hfresh, -, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hval : ValOfB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) (cl ρ η.wit 0 0 tv)
      (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) :=
    ValOf_monoB (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValB.store (η := CE η) ⟨hvc, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hx : ExtB η (η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto) :=
    Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := CE η) hnone h) (fun _ => Nat.le_refl _)
  have key : ∀ r ∈ tstep g mem pairs th, ∃ s' pw,
      (s', pw) ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i th.nalloc) us ws (stOf mem pairs th) ∧
      ∃ tys, r = (s'.mem, s'.pairs,
        { withS { th with term := e, env := (x, .ptr .own rt, [pw]) :: th.env } s' with tys := tys }) := by
    intro r hr
    obtain ⟨s1, t1, ws1, hm1, tys, rfl⟩ := TermRun.tstep_new_mem hterm hr
    simp only [evalOp, hea, hus, List.mem_map] at hm1
    obtain ⟨⟨s2, pw⟩, hal, he⟩ := hm1
    cases he
    exact ⟨_, _, hal, tys, rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := freshLabel g.lbase g.n g.i th.nalloc)
      (s := stOf mem pairs th) hlen
    simp only [tstep, hterm, evalOp, hea, hus, ne_eq, List.map_eq_nil_iff]
    exact List.ne_nil_of_mem hr
  · intro r hr
    obtain ⟨s', pw, hal, tys, rfl⟩ := key r hr
    obtain ⟨hmo', hoo', hpw⟩ := alloc_okPB hwcT hlen hval hfresh hnone hpl hpo.1 hpo.2.1 hpf0 hmo hoo ⟨s', pw⟩ hal
    obtain ⟨hg, -, hna, hpl', hful⟩ := alloc_growsP hpl ⟨s', pw⟩ hal
    obtain ⟨hwr, hhid⟩ := alloc_hidPB (s := stOf mem pairs th) hval
      (ShapeC_of_wc hwcT (by rw [List.length_map]; exact hlen))
      (by obtain ⟨_, h, -⟩ := wc_some hwcT; simp [h]) hfresh hpl ⟨s', pw⟩ hal
    simp only at hmo' hoo' hpw hg hna hwr hhid hpl' hful
    subst hpw
    have hwA : ∀ T o w, WordOKB (CE η) T o w →
        WordOKB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) T o w :=
      fun T o w h => WordOK_monoB (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _)
        (fun _ _ h' => h') (fun _ h' => h') h
    have hoh' : OwnHidPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem s'.vs
        s'.promises := by
      refine ⟨fun l c hc ho o hi => ?_, fun l c hc ho hlt => ?_⟩
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          rw [allocE_eq] at hc; cases hc; exact hhid o
        · rw [allocE_ne hl] at hc
          exact HiddenP_growsAtB (hoh.1 l c hc ho o hi) (hwA _ _) hwr hg hl hful
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
            (Nat.not_lt_zero _)
        · rw [allocE_ne hl] at hc
          obtain ⟨f, hf, hs, hH⟩ := hoh.2 l c hc ho hlt
          exact ⟨f, hf, fun hz => hs (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
            fun o hi => HiddenP_growsAtB (hH o hi) (hwA _ _) (Nat.le_refl _) hg hl hful⟩
    have hpd' : PubDefPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem
        s'.promises := by
      intro l c f hc hown hf o hi
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at hc; cases hc; exact (hown rfl).elim
      · rw [allocE_ne hl] at hc
        exact HiddenP_growsAtB (hpd l c f hc hown hf o hi) (hwA _ _) (Nat.le_refl _) hg hl hful
    have hpi' : PubInvB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      refine PubInv_growB (hbs := fun l hb h => by
          by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
          · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
          · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (alloc_pairs _ hal) hful rfl rfl (fun l c h => allocE_sub hnone h)
        (fun _ => Nat.le_refl _) rfl rfl (fun c h => by rw [allocE_eq] at h; rw [← Option.some.inj h]; rfl)
        (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
          (Nat.not_lt_zero _)) (hrcg := fun _ h => ⟨h, Nat.le_refl _⟩)
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl; exact Or.inr hpf0
        · rw [allocE_ne hl] at h; exact Or.inl h
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at h
        cases h
        refine Or.inr ?_
        rcases hseg with ⟨-, rfl, -⟩ | ⟨N, us0, j0, hT, -, -, -⟩
        · obtain ⟨vals, hcell, -⟩ := hoo' _ _ allocE_eq rfl
          rcases hcell with ⟨hwc, hv⟩ | hb
          · exact ⟨vals, hv, Option.some.inj (hwc.symm.trans (wc_of_accs hu'))⟩
          · obtain ⟨N, e0, us0, hT, -⟩ := hb
            exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
        · exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
      · rw [allocE_ne hl] at h; exact Or.inl ⟨h, hini⟩
    refine ⟨allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv),
      (by
        intro l c N u hf hc hty
        obtain ⟨j, hj, -, rfl⟩ := hf
        by_cases hl : freshLabel g.lbase g.n g.i j = freshLabel g.lbase g.n g.i th.nalloc
        · rw [hl, allocE_eq] at hc
          cases hc
          have h2 : cl ρ η.wit 0 0 tv = .array (.lit N) u := hty
          exact absurd hwcT (by rw [h2]; simp [wc, accs])
        · rw [allocE_ne hl] at hc
          have h0 : (CE η).sto (freshLabel g.lbase g.n g.i j) = none := (hfr.1 j hj).1
          rw [h0] at hc
          cases hc),
      cnE <| EFoot_freshB rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ tv,
        mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) tv 0 0 (use_mg hu htv),
        noIallV_cl (WitAF.ni hi.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu), trivial⟩ (alloc_newT hal hwcT) (alloc_undefT hal hwcT) l) (fun _ => .inl rfl)
        (fun _ => ⟨Nat.le_refl _, .inl rfl⟩),
      ⟨ρ, η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c', rfl,
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, ?_⟩
    · refine bind_FInvB hb (FInv_extB hE.2.1 hx hi1) ?_ ?_
      · simp only [VRF, VRb2]
        exact ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, ⟨cl ρ η.wit 0 0 tv, some η.tid⟩, by simp [cst, Promises.TVal.mk0], rfl,
          by simp [TEnv.withStoB, allocE, CE], .refl, rfl,
          show accs (cl ρ η.wit 0 0 tv) ≠ none from fun h => by simp [wc, h] at hwcT⟩
      · refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs],
          ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, by simp [cst, Promises.TVal.mk0]⟩, ?_⟩
        · show Ty.ptr (skelM .own) (etok (skel rt)) = Ty.ptr _ _
          rw [hl.2.1]; rfl
        · show Ty.ptr (modeC 0 .own) (etok (lyt 0 rt)) = Ty.ptr _ _
          rw [hl.2.2.2.2]; rfl
    have hopub' : OwnPubV (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      intro l c f hc ho hf
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
      · rw [allocE_ne hl] at hc
        exact ((hopub.alloc hpl hal) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
          fun a ha hi c1 N1 e1 us1 h1 => hi c1 N1 e1 us1 (by rw [allocE_ne (fun e => hl (ha.symm.trans e))]; exact h1))
    · refine ⟨hmo', hoo', hpl', ⟨fun j hj => ?_, PrivCoh_growsAtB hfr.2
          (fun a hu hl => by
            obtain ⟨c, N, e, us, hc, rest⟩ := hu
            exact ⟨c, N, e, us, by rw [allocE_ne hl] at hc; exact hc, rest⟩)
          hoo' hg hful (fun t m _ _ hu hl => by
            obtain ⟨c, N, e, us, hc, -, -, hT, -⟩ := hu
            rw [hl, allocE_eq] at hc; cases hc
            simp only at hT; rw [hT] at hwcT; simp [wc, accs] at hwcT)⟩, ?_, hoh', hpd', hopub', hpi',
        BoxInv_alloc hbi rfl hpl hpo.1 hal rfl rfl (fun _ hl => allocE_ne hl) (fun _ _ => rfl),
        PromOK_alloc hpo hpl hal⟩
      rotate_left 1
      · have e : s'.vs.vRelSt = (stOf mem pairs th).vs.vRelSt := alloc_relSt _ hal
        exact (SeenLE.mono hsn (Nat.le_of_eq e.symm) : SeenLE (CE η) s'.vs.vRelSt)
      · have hj' : th.nalloc ≤ j := by
          have : s'.nalloc ≤ j := hj
          rw [hna] at this; exact Nat.le_of_succ_le this
        obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
        have hne : freshLabel g.lbase g.n g.i j ≠ freshLabel g.lbase g.n g.i th.nalloc := fun h => by
          have := freshLabel_inj_k hn h; subst this
          have : s'.nalloc ≤ th.nalloc := hj
          rw [hna] at this; exact absurd this (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
        refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, f4, f5⟩
        change s'.mem[t]? = some m at ht
        by_cases hlt : t < (stOf mem pairs th).mem.size
        · rw [hg.2.1 t hlt] at ht
          have hp := f2 t m ht hl
          refine Classical.byContradiction fun hn' => ?_
          obtain ⟨m', hm', e⟩ := hful t hp hn'
          rw [ht] at hm'; cases hm'
          exact hne (hl.symm.trans e)
        · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
end
end TermStep.Flat

-- PORTB TermStep.lean:6083 tstepM_new
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  (tstepM_newABN (hDy := hDy) (hterm := hterm) (hniA := hniA) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS)).imp id
    fun h r hr => (h r hr).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:7173 tstep_fld
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_fldBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {i : Nat} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.fld i a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      obtain ⟨rt, ws, hev, hf⟩ := fld_stepB (g := g) (s := stOf mem pairs th) hop hi htv (fun k => (hE.2.1 k).1)
      have key : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) (.fld i a)).map
          fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
        simp [tstep, hterm]
      rw [key, hev]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst hr
      exact ⟨ρ, η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, hf, retPwN_skel hPS hRP (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:7194 tstepM_fld
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_fldBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {i : Nat} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.fld i a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT' := hT
  rw [hterm] at hT'
  cases hT' with
  | let_ hop _ =>
      obtain ⟨rt, ws, hev, -⟩ := fld_stepB (g := g) (s := stOf mem pairs th) hop hi htv (fun k => (hE.2.1 k).1)
      exact liftBN hm (tstep_fldBN (hDy := hDy) hterm hP hT hi hE htv hRP hPS) (same_let hterm (fun _ _ _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun r hr => by
          rw [hev, List.mem_singleton] at hr; subst hr; exact same_of_eq rfl))
end
end TermStep.Flat

-- PORTB TermStep.lean:7335 tstep_idx
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_idxBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.idx b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      obtain ⟨rt, ws, hev, hf⟩ := idx_stepB (g := g) (s := stOf mem pairs th) hop hi htv
      have key : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) (.idx b i)).map
          fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
        simp [tstep, hterm]
      rw [key, hev]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst hr
      exact ⟨ρ, η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, hf, retPwN_skel hPS hRP (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:7356 tstepM_idx
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_idxBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.idx b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT' := hT
  rw [hterm] at hT'
  cases hT' with
  | let_ hop _ =>
      obtain ⟨rt, ws, hev, -⟩ := idx_stepB (g := g) (s := stOf mem pairs th) hop hi htv
      exact liftBN hm (tstep_idxBN (hDy := hDy) hterm hP hT hi hE htv hRP hPS) (same_let hterm (fun _ _ _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun r hr => by
          rw [hev, List.mem_singleton] at hr; subst hr; exact same_of_eq rfl))
end
end TermStep.Flat

-- PORTB TermStep.lean:8670 tstepM_loadOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadOwnBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hnwc : wordOf (close th.σs (.ptr .own u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv (bind_opaqueOK hb)
  have hwr : wordOf (Ty.ptr .own ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:8723 tstepM_storeOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeOwnBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeB hm hsto hown husA hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:8785 tstepM_xchgOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgOwnBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th) → PromAbove r1.1 →
      MemInvB g (CE η) r1.1 :=
    fun r1 h hp1 => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := false)
    us wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeB (hm1 (s1, old) h1 hp1) hsto hown husA hval hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:9083 tstepM_loadLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .own u) = some (.own, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .own ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := acq)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (cell_lyt hl.2.2.2.2 rfl rfl).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:9855 tstepM_storeLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi hpk htv ho hwcu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB hm hsto hown hat hini hna hval hwUA hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:9918 tstepM_xchgLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig (sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1))]
    exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi hpk htv ho hwcu
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ad false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInvB g (CE η) r1.1 :=
    fun r1 h hp1 => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := false)
    us wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (hm1 (s1, old) h1 hp1) hsto hown hat hini hna hval hwUA hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10068 tstepM_loadAt
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadAtBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.loadAt b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAt hp hbuf hint hlt hltk _ hb =>
  obtain ⟨t, u, n, k, j, hp, hbuf, hint, hlt, hltk, hb⟩ : ∃ t u n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧ cx.bind x u = .ok c' :=
    ⟨_, _, _, _, _, hp, hbuf, hint, hlt, hltk, hb⟩
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, hini, hsku, hsig, htbS, -⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk (bind_opaqueOK hb)
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htbS (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ur, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10108 tstepM_xchgAt
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgAtBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAt b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, n, k, j, tv, c₁, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u ∧ c₁.bind x u = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, hini, hsku, hsig, htb, -⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 s1).map fun s2 => (s2, ur, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th) → PromAbove r1.1 →
      MemInvB g (CE η) r1.1 := fun r1 h hp1 => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := w)
    (a := offs ad (ev ρ j * nWords us)) (rel := false) us wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j * nWords us)) (hm1 (s1, old) h1 hp1) hsto hown hat hini hna hval hwUA hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10295 tstepM_loadAtF
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadAtFBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.loadAtF b i q) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAtF hp hbuf hct hop hint hlt hltk _ hb =>
  obtain ⟨t, u, c, n, k, j, hp, hbuf, hct, hop, hint, hlt, hltk, hb⟩ : ∃ t u c n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧ IntIdx cx i j ∧
      LtI cx j n ∧ LtI cx j k ∧ cx.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hb⟩
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, -, hsku, hsig, htbS, hiniF⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  obtain ⟨cs, hcs, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat' (hiniF o _ hato) hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) (tb_compTy q u c hct htbS) (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco))
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, cR, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, hco, hcs, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10339 tstepM_xchgAtF
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgAtFBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAtF hp hbuf hct hop _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, c, n, k, j, tv, c₁, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u c n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧
      IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv c ∧ c₁.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK c = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, -, hsku, hsig, htbu, hiniF⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct htbu
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  have hiniC := hiniF o _ hato
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨cs, hcs, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat' hiniC hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco))
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsgc hcs
  have hwUA : accs (cl ρ η.wit 0 0 c) = some cs := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco)).symm.trans hcs
  have hwU : wc (cl ρ η.wit 0 0 c) = some (nWords cs) := by rw [← wc_of_sig hsgc]; simp [wc, hcs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us + o)) false cs wsv 0 s1).map fun s2 => (s2, cR, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus, hco, hcs]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th) → PromAbove r1.1 →
      MemInvB g (CE η) r1.1 := fun r1 h hp1 => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := w)
    (a := offs ad (ev ρ j * nWords us + o)) (rel := false) cs wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j * nWords us + o)) (hm1 (s1, old) h1 hp1) hsto hown hat' hiniC hna hval hwUA hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10938 tstepM_bufInitB
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_bufInitBBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hZ : ZOK g (CE η) th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', EFootCN g th (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ ThInvEBN g.lbase g.n g.i p E' r.2.2 ∧
        MemInvB g E' (stOf r.1 r.2.1 r.2.2) ∧ BufInitBump th b i E' := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | bufInit hu hbuf hint heq hlt hu2 hsub hb =>
  obtain ⟨t, tv, u, n, k, j, c₁, c₂, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩ : ∃ t tv u n k j c₁ c₂,
      cx.use b = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx c₁ i j ∧ EqI c₁ j k ∧
      LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u ∧
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩
  have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
    unfold bufOf at hbuf; split at hbuf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
    · simp at hbuf
  subst ht
  have htu := use_TvOK hu htv
  obtain ⟨hi1, rb, wsb, hea, hvb, hlb⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨hi2, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu2 hi1
  have hJK : ev ρ j = ev ρ k := heq ρ hi1.1
  have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hi1.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hvb0 := hvb
  simp only [VRF, VRb2] at hvb
  obtain ⟨hv, hir⟩ := hvb
  rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmode, hini0⟩
  · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
    simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
    omega
  obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
  obtain ⟨w, rfl, hwv⟩ := map_singleton hws
  have hKi : ev ρ k ≤ η.ini ad.label := by
    simp only [IniR] at hir; exact Nat.le_trans (hir.1 ad (by simp [hwv])) (TEnv.selIni_le_ini _ _ _)
  have hKm : ev ρ k ≤ η.rc ad.label := by
    simp only [IniR] at hir; have h := hir.1 ad (by simp [hwv]); rw [TEnv.selIni_loc] at h; exact h
  have hat := hat0
  have hini := hini0
  simp only [cl, clI_zero] at hat hini
  
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, -, hsu⟩ := buf_runtime' hs'
  
  have htb1 : tb c₁.ke.length u = true := by
    have h := htu.2.1
    rw [← htu.2.2] at h
    simp [tb] at h
    exact h
  have ho : c₁.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu2).1)
  have hsig : sig ur = sig (cl ρ η.wit 0 0 u) := by
    have e1 : sig ur = sig (close th.σs u) := sig_of_eskel hsu
    rw [e1]; exact sig_WitL hi1.2.2.2.1 ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)
  obtain ⟨us0, hus0⟩ : ∃ us, accs (cl ρ η.wit 0 0 u) = some us := by
    rcases AtOff_lay hat with h | ⟨n', e', he', h⟩
    · simp [accs] at h
    · simp only [Ty.array.injEq] at he'; rw [he'.2]
      exact Option.ne_none_iff_exists'.1 h
  obtain ⟨us, hus⟩ : ∃ us, accs ur = some us := by
    have : wc ur ≠ none := by rw [wc_of_sig hsig]; simp [wc, hus0]
    cases h : accs ur with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have hweA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi1.2.2.2.1 hi1.2.2.2.2.1 ho htb1 (buf_lyt hlb.2.2.2.2 rfl).2).symm.trans hus
  have hwe : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨hval, hlen⟩ := ownStoreValB (cx := c₁) hE.2.1 hi1.2.2.2.1 hi1.2.2.2.2.1 hi2.1 hsub ho htb1 hvv hlv hsig hus
  
  let ini' := bumpIni η.ini ad.label (ev ρ j + 1)
  let rini' := bumpIni η.rini ad.label (ev ρ j + 1)
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  have hile : ∀ l, η.ini l ≤ ini' l := bumpIni_le η.ini ad.label (ev ρ j + 1)
  have hx : ExtB η (η.withStoB η.sto ini' (Ri := rini')) := Ext_withStoB hE.2.1 (fun l c h => h) hile (Ri := rini') (hRi := hri')
  let rtR : Ty := Ty.refine (Ty.loc μr (Ty.array nr ur)) (Pred.ini (Idx.lit (ev ρ j + 1)))
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, rtR, [w]) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, numOf, hwi, addrOf, hwv, bufElem, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := w)
    (a := offs ad (ev ρ j * nWords us)) (rel := false) us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr hpa => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hvr : (VRF False) ρ (η.withStoB η.sto ini' (Ri := rini')) (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      (shp rtR) [w] := by
    have h1 := VR_extB hE.2.1 hx hvb0
    simp only [VRF, VRb2] at h1 ⊢
    refine ⟨h1.1, fun a ha => ?_, fun hp => by obtain ⟨_, _, h⟩ := hp; simp [pp] at h⟩
    have hav : a = ad := by simp [hwv] at ha; exact ha.symm
    subst hav
    show ev ρ (.add k (.lit 1)) ≤ min (bumpIni η.ini a.label (ev ρ j + 1) a.label)
      (bumpIni η.rini a.label (ev ρ j + 1) a.label)
    rw [bumpIni_self, bumpIni_self]; simp [ev]; omega
  have hlay : Lay th.σs (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      rtR [w] := Lay_repred hlb
  exact ⟨CE (η.withStoB η.sto ini' (Ri := rini')), cnF (fun l _ hnb =>
      have hne : l ≠ ad.label := fun hl => hnb ⟨x, b, i, v, e, _, [w], ad, hterm, hea, by simp [hwv], hl.symm⟩
      ⟨Nat.le_of_eq (bumpIni_other _ _ _ _ hne), Nat.le_of_eq (bumpIni_other _ _ _ _ hne)⟩) <| EFoot_iniB (harr := .inr (ArrAt_of_bufB hm hsto hmode hat)) rfl rfl rfl rfl rfl rfl ⟨c, hsto, hmode⟩
      (hz := by
        by_cases hzl : g.zf ad.label
        · by_cases hpf : (CE η).pfr ad.label = none
          · exact .inr (.inl hpf)
          · have hlo : ev ρ j < η.ini ad.label ∧ ev ρ j < η.rini ad.label := by
              by_cases hrc : (CE η).rc ad.label ≤ ev ρ j
              · exact hZ _ ⟨x, b, i, v, e, _, w, ad, 0, hterm, hea, hwv, rfl⟩ hzl x b i v e hterm _ w ad _ wi (ev ρ j)
                  hea hwv hei (by simp [numOf, hwi]) rfl hpf hrc
              · have h := hKm; change ¬ (min (η.ini ad.label) (η.rini ad.label) ≤ ev ρ j) at hrc
                unfold TEnv.rc at h; omega
            refine .inr (.inr ⟨?_, ?_⟩)
            · show bumpIni η.ini ad.label (ev ρ j + 1) ad.label = η.ini ad.label
              rw [bumpIni_self]; omega
            · show bumpIni η.rini ad.label (ev ρ j + 1) ad.label = η.rini ad.label
              rw [bumpIni_self]; omega
        · exact .inl hzl)
      (hfz := fun _ => by
        show bumpIni η.ini ad.label (ev ρ j + 1) ad.label = η.ini ad.label ∨ η.ini ad.label ≤ η.rini ad.label
        have h := hKm; unfold TEnv.rc at h; rw [bumpIni_self]; omega)
      (fun l => ite_ini_cases _ _ _ l)
      (riniW_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hini hweA
        (show ev ρ j ≤ η.rc ad.label by omega) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) s' hs'), ⟨ρ, η.withStoB η.sto ini' (Ri := rini'), c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
      bind_FInvB hb (FInv_extB hE.2.1 hx hi2) hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
      (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
      (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
    fun rt' w' ad' rti' wi' n' he' hw' hei' hn' => by
      rw [hea] at he'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at he'
      obtain ⟨-, rfl⟩ := he'
      rw [hwv] at hw'
      cases hw'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hei'
      obtain ⟨-, rfl⟩ := hei'
      have hn : n' = ev ρ j := by simp [numOf, hwi] at hn'; exact hn'.symm
      subst hn
      show ev ρ j + 1 ≤ bumpIni η.ini ad.label (ev ρ j + 1) ad.label ∧
        ev ρ j + 1 ≤ bumpIni η.rini ad.label (ev ρ j + 1) ad.label
      rw [bumpIni_self, bumpIni_self]; exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:11091 tstepM_bufInit
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_bufInitBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hZ : ZOK g (CE η) th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨h1, h2⟩ := tstepM_bufInitBBN (hDy := hDy) hterm hP hT hi hE htv hm hZ hRP hPS
  exact ⟨h1, fun r hr hpa => let ⟨E', a1, a2, a3, _⟩ := h2 r hr hpa; ⟨E', a1, a2, a3⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:12452 tstepM_newBufA
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newBufABN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFABN p g ρ η th (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | newBuf hwf hsc hop haf hint hb =>
  rename_i k
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hi.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hlay : accs (close th.σs τ) ≠ none := accs_close hwf hi.2.2.2.2.1 haf hi.2.2.2.2.2.1.2.2
  obtain ⟨us, hus⟩ : ∃ us, accs (close th.σs τ) = some us := Option.ne_none_iff_exists'.1 hlay
  
  have hr : ∀ k, τ.guardT k = false → k < th.σs.length := lt_of_guardT (tb_of_wf τ hwf) hi.2.2.2.2.1
  have hsig : sig (close th.σs τ) = sig (cl ρ η.wit 0 0 τ) := sig_WitL hi.2.2.2.1 ρ hop hr
  have hwT : wc (cl ρ η.wit 0 0 τ) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨usT, husT⟩ : ∃ usT, accs (cl ρ η.wit 0 0 τ) = some usT := by
    cases h : accs (cl ρ η.wit 0 0 τ) with
    | none => simp [wc, h] at hwT
    | some usT => exact ⟨usT, rfl⟩
  have hnw : nWords usT = nWords us := by rw [wc_of_accs husT] at hwT; exact Option.some.inj hwT
  have hafT : (cl ρ η.wit 0 0 τ).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af τ 0 0 haf
  have hafR : (close th.σs τ).arrFree = true := by rw [← arrFree_sig, hsig, arrFree_sig]; exact hafT
  
  let z : Option (List WeakMem.Val) := if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none
  have hzv : ∀ zs, z = some zs → ValOfB η (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ wc (cl ρ η.wit 0 0 τ) = some zs.length := by
    intro zs h
    simp only [z] at h
    split at h
    · exact zero_valOfB hi.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.1 ρ hop hr haf ‹_› h
    · cases h
  have hstat : zeroableIn [] cx.ke τ = true → z.isSome = true := by
    intro h
    have hR := KindSound.zero_close cx.ke th.σs τ hi.2.2.2.2.2.1.2.1 h
    obtain ⟨zs, hzs, -⟩ := zpB _ _ (Nat.lt_succ_self _) [] [] hafR knone_nil hR
    simp [z, hR, hzs]
  
  let K := ev ρ k
  let lbl := freshLabel g.lbase g.n g.i th.nalloc
  let iv : Nat := if z.isSome then K else 0
  let ini' := bumpIni η.ini lbl iv
  let rini' := bumpIni η.rini lbl iv
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  let E0 := CE (η.withStoB η.sto ini' (Ri := rini'))
  let T := Ty.array (.lit K) (cl ρ η.wit 0 0 τ)
  let E' := allocE E0 lbl T
  let η' := η.withStoB E'.sto ini' (Ri := rini')
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, hi0, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hnone0 : E0.sto lbl = none := hnone
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := E0) hnone0 h) (bumpIni_le _ _ _)
    (Ri := rini') (hRi := hri')
  let rtR : Ty := .refine (.loc .own (.array (.lit K) (close th.σs τ))) (.ini (.lit iv))
  let R := allocBuf lbl (K * nWords us) z (stOf mem pairs th)
  have key : tstep g mem pairs th =
      [(R.1.mem, R.1.pairs, withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1)] := by
    simp only [tstep, hterm, evalOp, hei, numOf, hus, Option.bind_eq_bind, Option.bind_some, hwi]; rfl
  rw [key]
  refine ⟨by simp, fun r hr' => ?_⟩
  simp only [List.mem_singleton] at hr'
  subst hr'
  have hpw : R.2 = cst (.loc ⟨lbl, 0⟩ 0) := rfl
  
  have hsub0 : ∀ l c, (CE η).sto l = some c → E0.sto l = some c := fun l c h => h
  have hile0 : ∀ l, (CE η).ini l ≤ E0.ini l := bumpIni_le η.ini lbl iv
  have hmo0 : MemOKPB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).promises :=
    MemOKP_monoB hmo rfl rfl hsub0 hile0 (fun t m c h hc => hc)
  have hmono0 : ∀ {U : Ty} {vs : List Word}, ValOfB (CE η) U vs → ValOfB E0 U vs :=
    fun h => ValOf_monoB (η₁ := CE η) (η₂ := E0) rfl rfl hsub0 hile0 h
  have hoo0 : OwnOKPFB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).vs
      (stOf mem pairs th).promises := by
    intro l c hc ho
    have hne : l ≠ lbl := fun h => by rw [h] at hc; rw [hnone0] at hc; cases hc
    exact OwnCellF_envB (hoo l c hc ho) hmono0 (bumpIni_other _ _ _ _ hne) rfl hmo.2.2 (bumpIni_other _ _ _ _ hne)
  have hi0' : η.ini lbl = 0 := hi0
  have hini : E0.ini lbl ≤ K := by
    show bumpIni η.ini lbl iv lbl ≤ K
    rw [bumpIni_self, hi0']
    refine Nat.max_le.2 ⟨Nat.zero_le _, ?_⟩
    simp only [iv]; split <;> omega
  have hini0 : 0 < E0.ini lbl → z ≠ none := by
    intro h hz0
    have : E0.ini lbl = 0 := by
      show bumpIni η.ini lbl iv lbl = 0
      rw [bumpIni_self, hi0']; simp [iv, hz0]
    omega
  have hzE : ∀ zs, z = some zs → ValOfB E' (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ zs.length = nWords usT :=
    fun zs h => ⟨ValOf_monoB (η₁ := η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (hzv zs h).1,
      by have := (hzv zs h).2; rw [hwT] at this; rw [hnw]; exact (Option.some.inj this).symm⟩
  have hab := allocBuf_okPB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
    (s := stOf mem pairs th) (η := E0) husT hzE
    hini hini0 hfresh hnone0 hpl hpo.2.1 hmo0 hoo0 hpf0
  rw [hnw] at hab
  obtain ⟨hmo', hoo', -⟩ := hab
  obtain ⟨hg, hpr, hna⟩ := allocBuf_grows lbl (K * nWords us) z (stOf mem pairs th)
  have hwE : ∀ T o w, WordOKB (CE η) T o w → WordOKB E' T o w := fun T o w h =>
    WordOK_monoB (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (fun _ _ h' => h') (fun _ h' => h') h
  have hiniE : ∀ l c o, l ≠ lbl → InitR E' c l o → InitR (CE η) c l o := fun l c o hl hi N1 e1 us1 h1 h2 => by
    have := hi N1 e1 us1 h1 h2
    rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  have hoh' : OwnHidPB E' R.1.mem R.1.vs R.1.promises := by
    refine ⟨?_, ?_⟩
    · intro l c hc ho o hi
      by_cases hl : l = lbl
      · rw [hl] at hc hi
        have hcT : c = ⟨T, some η.tid⟩ := by
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at hc; exact (Option.some.inj hc).symm
        subst hcT
        rw [hl]
        unfold HiddenPB
        intro t m hP hm hloc hnok
        exfalso
        rcases Option.eq_none_or_eq_some z with hzc | ⟨zs, hzc⟩
        · 
          have h0 : E'.ini lbl = 0 := by
            show bumpIni η.ini lbl iv lbl = 0
            rw [bumpIni_self, hi0']; simp [iv, hzc]
          have := hi K (cl ρ η.wit 0 0 τ) usT rfl husT
          rw [show E'.rc lbl = 0 by have := E'.rc_le_ini lbl; omega, Nat.zero_mul] at this; exact Nat.not_lt_zero _ this
        · 
          apply hnok
          by_cases hlt : t < (stOf mem pairs th).mem.size
          · rw [hg.2.1 t hlt] at hm
            exact (hP (hfresh t m hm (by rw [hloc]))).elim
          · have hw := allocBuf_newOKB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
              (s := stOf mem pairs th) (η := E0) husT hzE zs hzc t m (by omega) (by rw [hnw]; exact hm)
            rw [hloc] at hw; exact hw
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        exact HiddenP_growsAtB (hoh.1 l c hc ho o (fun N1 e1 us1 h1 h2 => by
            have := hi N1 e1 us1 h1 h2; rw [hrc] at this; exact this))
          (hwE _ _) (allocBuf_vWr_le _ _ _ _) hg hl
          (fun t h1 h2 => absurd h1 h2)
    · intro l c hc ho hlt
      by_cases hl : l = lbl
      · exfalso
        have h1 : E'.ini lbl ≤ E'.rini lbl := by
          show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl
          rw [bumpIni_self, bumpIni_self, hi0']; omega
        have h2 : E'.rc lbl = E'.ini lbl := Nat.min_eq_left h1
        rw [hl] at hlt; omega
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        have hie : E'.ini l = (CE η).ini l := bumpIni_other _ _ _ _ hl
        obtain ⟨f, hf, hsn', hH⟩ := hoh.2 l c hc ho (by rw [hrc, hie] at hlt; exact hlt)
        exact ⟨f, hf, fun hz => hsn' (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
          fun o hi => HiddenP_growsAtB (hH o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
          (fun t h1 h2 => absurd h1 h2)⟩
  have hpd' : PubDefPB E' R.1.mem R.1.promises := by
    intro l c f hc hown hf o hi
    by_cases hl : l = lbl
    · rw [hl] at hc
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at hc; cases hc; exact (hown rfl).elim
    · rw [allocE_ne hl] at hc
      exact HiddenP_growsAtB (hpd l c f hc hown hf o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
        (fun t h1 h2 => absurd h1 h2)
  have hopub' : OwnPubV E' R.1 := by
    intro l c f hc ho hf
    by_cases hl : l = lbl
    · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
    · rw [allocE_ne hl] at hc
      exact ((hopub.allocBuf hpl lbl (K * nWords us) z) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
        fun a ha hi c1 N1 e1 us1 h1 h2 h3 => by
          have hne : a.label ≠ lbl := fun e => hl (ha.symm.trans e)
          have := hi c1 N1 e1 us1 (by rw [allocE_ne hne]; exact h1) h2 h3
          rwa [show E'.rc a.label = (CE η).rc a.label from
            TEnv.rc_congr (bumpIni_other _ _ _ _ hne) (bumpIni_other _ _ _ _ hne)] at this)
  have hrcl : E'.rc lbl = E'.ini lbl := Nat.min_eq_left (show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl by
    rw [bumpIni_self, bumpIni_self, hi0']; omega)
  have hpi' : PubInvB E' R.1 := by
    refine PubInv_growB (E := CE η) (hbs := fun l hb h => by
        by_cases hl : l = lbl
        · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
        · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (fun _ h => h) (fun t h1 h2 => absurd h1 h2) rfl rfl
      (fun l c h => allocE_sub (η := E0) hnone0 (hsub0 l c h)) hile0 rfl rfl
      (fun c h => by
        have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
        rw [h2] at h; rw [← Option.some.inj h]; rfl)
      (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd hlt (by rw [hrcl]; exact Nat.lt_irrefl _))
      (hrcg := fun l h => by
        by_cases hl : l = lbl
        · rw [hl, hrcl] at h; exact absurd h (Nat.lt_irrefl _)
        · exact ⟨by rwa [TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl),
            show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl] at h,
            Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl)⟩)
      (hfi := fun l c h ho => by
        by_cases hl : l = lbl
        · rw [hl] at h
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at h; rw [← Option.some.inj h] at ho; exact absurd rfl ho
        · exact Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl))
    · by_cases hl : l = lbl
      · exact Or.inr (by rw [hl]; exact hpf0)
      · rw [allocE_ne hl] at h; exact Or.inl h
    by_cases hl : l = lbl
    · rw [hl] at h
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at h; cases h
      refine Or.inr ?_
      rcases hseg with ⟨-, rfl, -⟩ | ⟨N1, us1, j1, hT1, -, -, -⟩
      · simp [T, accs] at hu'
      · have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N1) S := hT1
        simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
        obtain ⟨-, rfl⟩ := hT2
        rw [husT] at hu'; obtain rfl := Option.some.inj hu'
        obtain ⟨-, jb, -, hjb, -⟩ := hini K (cl ρ η.wit 0 0 τ) rfl
        have hpos : 0 < E0.ini lbl := by
          rw [hl] at hjb; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hjb
        obtain ⟨zs, hzs⟩ := Option.ne_none_iff_exists'.1 (hini0 hpos)
        obtain ⟨h1, h2⟩ := hzE zs hzs
        exact ⟨zs.map cst, h1, by rw [List.length_map]; exact h2⟩
    · rw [allocE_ne hl] at h
      refine Or.inl ⟨h, fun N1 e1 h1 => ?_⟩
      have := hini N1 e1 h1
      rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  refine ⟨E', (by
    intro l c N u hf hc hty
    refine ⟨x, n, τ, e, hterm, ?_⟩
    obtain ⟨j, hj, -, rfl⟩ := hf
    by_cases hl : freshLabel g.lbase g.n g.i j = lbl
    · have hc2 : E'.sto lbl = some ⟨T, some E0.tid⟩ := allocE_eq
      rw [hl, hc2] at hc
      cases hc
      have h2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N) u := hty
      injection h2 with _ h3
      exact h3.symm
    · have hc2 : E'.sto (freshLabel g.lbase g.n g.i j) = E0.sto (freshLabel g.lbase g.n g.i j) := allocE_ne hl
      have h0 : E0.sto (freshLabel g.lbase g.n g.i j) = none := (hfr.1 j hj).1
      rw [hc2, h0] at hc
      cases hc),
    cnF (fun l hl _ => have hne : l ≠ lbl := fun e => hl (by subst e; exact hnone0)
      ⟨Nat.le_of_eq (bumpIni_other _ _ _ _ hne), Nat.le_of_eq (bumpIni_other _ _ _ _ hne)⟩) <|
    EFoot_freshB rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases (T := T) ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ (.array (.lit K) τ),
    mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [mg] using mg_of_wf τ hwf),
    noIallV_cl (WitAF.ni hi.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [noIallV] using hniA), trivial⟩
        (allocBuf_newT (lbl := lbl) (K := K) (z := z) (s := stOf mem pairs th) (e := cl ρ η.wit 0 0 τ) husT hnw)
        (allocBuf_undefT (lbl := lbl) (K := K) (z := z) (s := stOf mem pairs th) (e := cl ρ η.wit 0 0 τ) husT hnw
          (fun h0 => by
            cases hzz : zeroableIn [] [] (close th.σs τ) with
            | false =>
              show (if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none) = none
              simp [hzz]
            | true =>
              exact absurd ((zrel_zero _ _ [] [] (zrel_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ hop hr) hsig
                knone_nil).1 hzz) (by rw [h0]; simp))) l) (fun _ => .inl rfl)
      (fun l => ite_ini_cases _ _ _ l)
      (hrw := RiniW_of_ne fun l c h => bumpIni_other _ _ _ _ fun e => by
        subst e; cases h.symm.trans hnone0),
    ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', bind_FInvB hb (FInv_extB hE.2.1 hx hi) ?_ ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    hmo', hoo', fun t ht => Nat.lt_of_lt_of_le (hpl t ht) hg.1,
      ⟨fun j hj => ?_, PrivCoh_allocBufB hfr.2
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, ho, hp, hT, hus1, hle, hlt⟩ := hu
          refine ⟨c, N, e, us1, by rw [allocE_ne hl] at hc; exact hc, ho, hp, hT, hus1, ?_, hlt⟩
          rwa [TEnv.rc_congr (η' := E') (η := CE η) (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)] at hle)
        hoo' hfresh
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, -, -, hT, hus1, hle, hlt⟩ := hu
          rw [hl, show E'.sto lbl = some ⟨T, some η.tid⟩ from allocE_eq] at hc; cases hc
          have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N) e := hT
          simp only [Ty.array.injEq, Idx.lit.injEq] at hT2; obtain ⟨rfl, rfl⟩ := hT2
          refine Classical.byContradiction fun hz => ?_
          have hs : z.isSome = true := Option.ne_none_iff_isSome.1 hz
          have hrc : K ≤ E'.rc lbl := by
            show K ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
            have hiv : iv = K := by simp only [iv, hs, ↓reduceIte]
            rw [bumpIni_self, bumpIni_self, hiv]
            exact Nat.le_min.2 ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
          rw [hl] at hle
          have := Nat.mul_le_mul_right (nWords us1) hrc
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_trans this hle)) (Nat.lt_irrefl _))⟩, hsn, hoh', hpd', hopub', hpi',
      BoxInv_allocBuf hbi rfl rfl rfl (fun l hl => by rw [allocE_ne hl]; rfl) (fun l hl => bumpIni_other _ _ _ _ hl),
        PromOK_eq hpo rfl rfl⟩
  · 
    simp only [VRF, VRb2]
    refine ⟨Or.inr ⟨⟨lbl, 0⟩, ⟨T, some η.tid⟩, _, by simp [hpw, cst, Promises.TVal.mk0],
      (show E'.sto lbl = _ from allocE_eq), ?_, .refl, rfl, ?_⟩, ?_⟩
    · simp only [cl, clI_zero]; exact AtOff.here (Or.inr ⟨K, _, rfl, by simp [husT]⟩)
    · intro N' e' h; left; exact ⟨by simp only [cl, clI_zero]; rfl, rfl⟩
    · refine ⟨fun a ha => ?_, fun hp => by obtain ⟨_, _, h⟩ := hp; simp [pp] at h⟩
      have hav : a = ⟨lbl, 0⟩ := by simp [hpw, cst, Promises.TVal.mk0] at ha; exact ha.symm
      subst hav
      show ev ρ _ ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
      refine Nat.le_min.2 ⟨?_, ?_⟩
      · rw [bumpIni_self]
        split
        · rename_i hzs
          have h1 := hstat hzs
          have h2 : iv = K := by simp only [iv, h1, ite_true]
          rw [h2]; exact Nat.le_max_right _ _
        · exact Nat.zero_le _
      · rw [bumpIni_self]
        split
        · rename_i hzs
          have h1 := hstat hzs
          have h2 : iv = K := by simp only [iv, h1, ite_true]
          rw [h2]; exact Nat.le_max_right _ _
        · exact Nat.zero_le _
  · refine ⟨fun us' h => by simp [rtR, accs] at h; subst h; rfl, ?_, by simp [rtR, wc, accs], ?_, ?_⟩
    · simp [rtR, skel, close, substTs, skelM, rf]; rfl
    · simp only [rtR, Valid]; exact Or.inr ⟨⟨lbl, 0⟩, by simp [hpw, cst, Promises.TVal.mk0]⟩
    · simp [rtR, close, substTs, lyt, anyB_zero, idxC, ofMs, modeC]; rfl
  · have hj' : th.nalloc ≤ j := by
      have h1 : R.1.nalloc ≤ j := hj
      rw [hna] at h1; exact Nat.le_of_succ_le h1
    obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
    have hne : freshLabel g.lbase g.n g.i j ≠ lbl := fun h => by
      have := freshLabel_inj_k hn h; subst this
      have h1 : R.1.nalloc ≤ th.nalloc := hj
      rw [hna] at h1; exact absurd h1 (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
    refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, ?_,
      ⟨by show bumpIni η.rini lbl iv (freshLabel g.lbase g.n g.i j) = 0; rw [bumpIni_other _ _ _ _ hne]; exact f5.1, f5.2⟩⟩
    · change R.1.mem[t]? = some m at ht
      by_cases hlt : t < (stOf mem pairs th).mem.size
      · rw [hg.2.1 t hlt] at ht; exact f2 t m ht hl
      · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · show bumpIni η.ini lbl iv (freshLabel g.lbase g.n g.i j) = 0
      rw [bumpIni_other _ _ _ _ hne]; exact f4
end
end TermStep.Flat

-- PORTB TermStep.lean:12782 tstepM_newBuf
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newBufBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  (tstepM_newBufABN (hDy := hDy) (hterm := hterm) (hniA := hniA) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS)).imp id
    fun h r hr => (h r hr).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:13216 tstepM_inlBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inlBSBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPwN th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  have harmS : (armsOf (.sum rt (close th.σs τ)))[j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed (.sum rt (close th.σs τ)) = true := by simp [isBoxed, sumHead, hS]
  have hRa : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hstoL : η.sto lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num j) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum rt (close th.σs τ), [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := lbl) (us := .one :: us)
      (ws := cst (.num j) :: p0) (s := s) (by simp [nWords, Acc.size] at hnw ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    let B : Box := ⟨j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm hn hbf hal hnw.symm
    simp only at hpw
    subst hpw
    obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
    have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
    have eqw : VEq ws q' := eq1.symm.trans eq'.vals
    have hv2 : (VRF False) ρ η'.unsee t (shp rt) q' :=
      VR_extB hE.2.1.unsee (Ext_unseeB hx) (VR_storeB hE.2.1 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
        (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VR_upB (bkG := False) _ _ _ _ hwq hv))
    have hvr : (VRF False) ρ η' (.sum t τ) (shp (.sum rt (close th.σs τ))) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxLB (B := B) hS hRa rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) hj hq' hv2
        (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
        (by show ((armsOf (.sum rt (close th.σs τ)))[j]?).bind wc = some (p0.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hnw, List.length_map])
    refine ⟨CE η', fun _ => rfl, by rw [hCE]; exact cnE <| EFoot_seeBoxB (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)),
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPwN_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (Lay_box ⟨hshape, hsk, hwc, hval, hly⟩ hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13536 tstepM_inrBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inrBSBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPwN th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  let τc := close th.σs τ
  let n := (armsOf τc).length
  have harmS : (armsOf (.sum τc rt))[n + j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed (.sum τc rt) = true := by simp [isBoxed, sumHead, τc, hS]
  have hRb : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hstoL : η.sto lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num (n + j)) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum τc rt, [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box (t := Ty.sum (close th.σs τ) rt) (j := (armsOf (close th.σs τ)).length + j) hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := lbl) (us := .one :: us)
      (ws := cst (.num (n + j)) :: p0) (s := s) (by simp [nWords, Acc.size] at hnw ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    let B : Box := ⟨n + j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm hn hbf hal hnw.symm
    simp only at hpw
    subst hpw
    obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
    have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
    have eqw : VEq ws q' := eq1.symm.trans eq'.vals
    have hv2 : (VRF False) ρ η'.unsee t (shp rt) q' :=
      VR_extB hE.2.1.unsee (Ext_unseeB hx) (VR_storeB hE.2.1 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
        (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VR_upB (bkG := False) _ _ _ _ hwq hv))
    have hvr : (VRF False) ρ η' (.sum τ t) (shp (.sum τc rt)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxRB (B := B) hS hRb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) (Nat.le_add_right _ _)
        (by show ofArm rt (n + j - n) _ = _; rw [Nat.add_sub_cancel_left]; exact hq') hv2
        (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
        (by show ((armsOf (.sum τc rt))[n + j]?).bind wc = some (p0.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hnw, List.length_map])
    refine ⟨CE η', fun _ => rfl, by rw [hCE]; exact cnE <| EFoot_seeBoxB (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)),
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPwN_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (TermSound.Lay_boxR ⟨hshape, hsk, hwc, hval, hly⟩ hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13652 tstepM_inlBBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inlBBSBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP1 : RetPwN th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hv
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let S := Ty.sum rt (close th.σs τ)
  have harmS : (armsOf S)[B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S r1.2.1 r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num B0.tag) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  unfold PAx at hpx
  rw [key] at hpx
  rw [key]
  refine ⟨?_, ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨r1, h1, hp1⟩ := hne h0
    have hlen : r1.2.2.length = nWords us := by rw [← ((hpr r1 h1).2 hp1).2.1.length, hnw]
    obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i r1.1.nalloc) (us := .one :: us)
      (ws := cst (.num B0.tag) :: r1.2.2) (s := r1.1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    have hmem : ((injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1)) ≠ [] := by
      rw [hinj r1 h1 hp1, List.map_map]; exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
    intro hnil; rw [List.flatMap_eq_nil_iff] at hnil; exact hmem (hnil r1 h1)
  · intro r hr hpr0
    rw [List.mem_flatMap] at hr
    obtain ⟨r1, h1, hr⟩ := hr
    have hp1 : PromAbove r1.1 := by
      obtain ⟨f1, f2⟩ := (hpr r1 h1).1
      have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
      have hpa' := hpr0
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
      exact injM_pa hpl1 hr2 hpa'
    obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
    rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    obtain ⟨s1, j1, p1⟩ := r1
    simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
    have hm1 : MemInvB g (CE η) s1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
    have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
    simp only at hpw
    subst hpw
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    have hv0 : (VRF False) ρ η' t (vsh 0 (shp rt)) [w] := by rw [vsh_zero rt hrb]; exact VR_extB hE.2.1 hx hv
    have hv1 : (VRF False) ρ η' t (vsh 0 (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_renB (B1 := B0) (B2 := B) hx.1 hw rfl rfl
        (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
        (by simpa [η', TEnv.withStoB] using hsto0)
        (by simp [η', TEnv.withStoB, hini0]) rfl (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
        (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
        (by simp [η', TEnv.withStoB, hini0])
    have hvr : (VRF False) ρ η' (.sum t τ) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxLBB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) hj hv1
        (by show ((armsOf S)[B0.tag]?).bind wc = some (p1.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hlen, List.length_map])
    refine ⟨CE η', fun _ => rfl, cnC (s1 := s1) (by rw [hCE]; exact cnE <| EFoot_seeBoxB (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1,
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPwN_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (Lay_box hl hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13773 tstepM_inrBBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inrBBSBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP1 : RetPwN th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hv
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let n := (armsOf (close th.σs τ)).length
  let S := Ty.sum (close th.σs τ) rt
  have harmS : (armsOf S)[n + B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S (n + r1.2.1) r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num (n + B0.tag)) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  unfold PAx at hpx
  rw [key] at hpx
  rw [key]
  refine ⟨?_, ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨r1, h1, hp1⟩ := hne h0
    have hlen : r1.2.2.length = nWords us := by rw [← ((hpr r1 h1).2 hp1).2.1.length, hnw]
    obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i r1.1.nalloc) (us := .one :: us)
      (ws := cst (.num (n + B0.tag)) :: r1.2.2) (s := r1.1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    have hmem : ((injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1)) ≠ [] := by
      rw [hinj r1 h1 hp1, List.map_map]; exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
    intro hnil; rw [List.flatMap_eq_nil_iff] at hnil; exact hmem (hnil r1 h1)
  · intro r hr hpr0
    rw [List.mem_flatMap] at hr
    obtain ⟨r1, h1, hr⟩ := hr
    have hp1 : PromAbove r1.1 := by
      obtain ⟨f1, f2⟩ := (hpr r1 h1).1
      have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
      have hpa' := hpr0
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
      exact injM_pa hpl1 hr2 hpa'
    obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
    rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    obtain ⟨s1, j1, p1⟩ := r1
    simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
    have hm1 : MemInvB g (CE η) s1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
    have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
    simp only at hpw
    subst hpw
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨n + B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    have hv0 : (VRF False) ρ η' t (vsh 0 (shp rt)) [w] := by rw [vsh_zero rt hrb]; exact VR_extB hE.2.1 hx hv
    have hv1 : (VRF False) ρ η' t (vsh n (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_renB (B1 := B0) (B2 := B) hx.1 hw rfl rfl
        (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
        (by simpa [η', TEnv.withStoB] using hsto0)
        (by simp [η', TEnv.withStoB, hini0]) (show B0.tag + n = (n + B0.tag) + 0 by omega) (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
        (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
        (by simp [η', TEnv.withStoB, hini0])
    have hvr : (VRF False) ρ η' (.sum τ t) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxRBB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) (Nat.le_add_right _ _) hv1
        (by show ((armsOf S)[n + B0.tag]?).bind wc = some (p1.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hlen, List.length_map])
    refine ⟨CE η', fun _ => rfl, cnC (s1 := s1) (by rw [hCE]; exact cnE <| EFoot_seeBoxB (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1,
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPwN_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (TermSound.Lay_boxR hl hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13898 tstepM_inlTS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inlTSBN {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    have htv' := OpT_TvOK hP hop htv
    cases hop with
    | inl _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum t τ) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      have hsk : (Ty.sum rt (close th.σs τ)).tier = (close th.σs (.sum _ τ)).tier :=
        tier_of_eskel (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum t τ) = .ok c'' → Typed p c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨he, htv'⟩
      by_cases hS : (Ty.sum rt (close th.σs τ)).tier = .boxed
      · cases hrb : isBoxed rt with
        | false => exact paW <| tstepM_inlBSBN (hDy := hDy) (hbf := hbf) (hRP1 := retPwN_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb hE hm
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepM_inlBBSBN (hDy := hDy) (hbf := hbf) (hRP1 := retPwN_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb
              (lay_closed hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl) hE hm hpx
      · refine paW <| tstepM_inlSBN (hDy := hDy) hterm hP (fun t' c₁' hu' => ?_) hT hi hE htv hm hRP hPS
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← hsk]; exact hS
end
end TermStep.Flat

-- PORTB TermStep.lean:13933 tstepM_inlT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inlTBN {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  (tstepM_inlTSBN (hDy := hDy) (hRP := hRP) (hPS := hPS) (hterm := hterm) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hbf := hbf) (hpx := hpx)).imp id
    fun h r hr hp => (h r hr hp).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:13943 tstepM_inrTS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inrTSBN {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    have htv' := OpT_TvOK hP hop htv
    cases hop with
    | inr _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum τ t) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      have hsk : (Ty.sum (close th.σs τ) rt).tier = (close th.σs (.sum τ _)).tier :=
        tier_of_eskel (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum τ t) = .ok c'' → Typed p c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨he, htv'⟩
      by_cases hS : (Ty.sum (close th.σs τ) rt).tier = .boxed
      · cases hrb : isBoxed rt with
        | false => exact paW <| tstepM_inrBSBN (hDy := hDy) (hbf := hbf) (hRP1 := retPwN_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb hE hm
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepM_inrBBSBN (hDy := hDy) (hbf := hbf) (hRP1 := retPwN_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb
              (lay_closed hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl) hE hm hpx
      · refine paW <| tstepM_inrSBN (hDy := hDy) hterm hP (fun t' c₁' hu' => ?_) hT hi hE htv hm hRP hPS
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← hsk]; exact hS
end
end TermStep.Flat

-- PORTB TermStep.lean:13978 tstepM_inrT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inrTBN {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  (tstepM_inrTSBN (hDy := hDy) (hRP := hRP) (hPS := hPS) (hterm := hterm) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hbf := hbf) (hpx := hpx)).imp id
    fun h r hr hp => (h r hr hp).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:13996 case_armNBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem case_armNBSBN {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 q1 : List Word}
    (hb : c₁.bind xv u = .ok c') (he : Typed p c' e') (htv : TvOK c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env) (hE : EnvOKB p η) (hm1 : MemInvB g (CE η) s1)
    (hty : isBoxed ty = false) (hq : ofArm ty j p1 = some q1) (hlay : Lay th.σs u ty q1)
    (hvr : (VRF False) ρ η u (shp ty) q1) (hRP1 : RetPwN th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e') :
    injM g s1 ty j p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ty j p1,
      ThInvMFSBN p g (CE η) s1 th r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) := by
  rw [injM_nbB hty, hq]
  refine ⟨by simp [ol], fun r2 hr2 => ?_⟩
  simp [ol] at hr2; subst hr2
  exact ⟨CE η, fun _ => rfl, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv, by simpa [withS] using bind_FInvB hb hi1 hvr hlay, retPwN_eq hRP1 (bind_ret hb), hDy⟩, hm1⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:14023 case_armBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem case_armBSBN {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 : List Word} {us : List Acc} {w : Word}
    {x0 : Address} {B0 : Box} {s0 : Nat}
    (hb : c₁.bind xv u = .ok c') (he : Typed p c' e') (htv : TvOK c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env) (hE : EnvOKB p η) (hm1 : MemInvB g (CE η) s1)
    (hn : 0 < g.n) (hbf : g.boxFence = true) (hty : isBoxed ty = true) (hus : (armsOf ty)[j]?.bind accs = some us)
    (hlen : p1.length = nWords us) (hw : w.val = .loc x0 0) (hB0 : η.box x0.label = some B0)
    (hsto0 : η.sto x0.label = none) (hini0 : η.ini x0.label = 0) (ht : B0.tag = j + s0)
    (hWp : WLe B0.pay p1) (hv : (VRF False) ρ η u (vsh s0 (shp ty)) [w]) (hlay : ∀ pw, Lay th.σs u ty [pw]) (hRP1 : RetPwN th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e') :
    injM g s1 ty j p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ty j p1,
      ThInvMFSBN p g (CE η) s1 th r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) := by
  rw [injM_box hty hus]
  refine ⟨?_, fun r2 hr2 => ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i s1.nalloc) (us := .one :: us)
      (ws := cst (.num j) :: p1) (s := s1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · rw [List.mem_map] at hr2
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr2
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
    simp only at hpw
    subst hpw
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨j, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    have hv0 : (VRF False) ρ η' u (vsh s0 (shp ty)) [w] := VR_extB hE.2.1 hx hv
    have hv1 : (VRF False) ρ η' u (vsh 0 (shp ty)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_renB (B1 := B0) (B2 := B) hx.1 hw rfl rfl
        (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
        (by simpa [η', TEnv.withStoB] using hsto0)
        (by simp [η', TEnv.withStoB, hini0]) (by show B0.tag + 0 = j + s0; omega)
        (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS) (bh_shp ty hty) hv0
        (by simp [η', TEnv.withStoB, hini0])
    rw [vsh_zero ty hty] at hv1
    refine ⟨CE η', fun _ => rfl, by rw [hCE]; exact cnE <| EFoot_seeBoxB (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)),
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv, ?_, retPwN_eq hRP1 (bind_ret hb), hDy⟩, ?_⟩
    · simpa [withS] using bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hv1 (hlay _)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:14095 tstepM_caseBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_caseBSBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty} {c₁ c₂ c₃ : Cx}
    {ra rb : Ty} {ws : List Word} (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hb1 : c₁.bind x u = .ok c₂) (he1 : Typed p c₂ e₁) (htv1 : TvOK c₂)
    (hb2 : c₁.bind y v = .ok c₃) (he2 : Typed p c₃ e₂) (htv2 : TvOK c₃)
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (.sum ra rb, ws)) (hv : (VRF False) ρ η (.sum u v) (shp (.sum ra rb)) ws)
    (hl : Lay th.σs (.sum u v) (.sum ra rb) ws) (hS : (Ty.sum ra rb).tier = .boxed)
    (hsg : sig (.sum ra rb) = sig (cl ρ η.wit 0 0 (.sum u v)))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP1 : RetPwN th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  have hrb : isBoxed (.sum ra rb) = true := by simp [isBoxed, sumHead, hS]
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hv
  
  have hv' := hv
  simp only [VRF, VRb2, shp] at hv'
  obtain ⟨n0, Ra, Rb, hR, hv'⟩ := hv'
  simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
  obtain ⟨rfl, rfl, rfl⟩ := hR
  have htl : (Ty.sum (lnorm ra) (lnorm rb)).tier = .boxed := by
    rw [← hS]; exact tier_lnorm (.sum ra rb)
  have hv3 := hv'.resolve_right (fun ⟨j, p, hd, _, _⟩ => by rw [htl] at hd; simp [decodeArm] at hd)
  obtain ⟨-, x1, s0, B, hx1, -, hB, hn1, -, -, hA, hB'⟩ := hv3
  rw [wc_boxed hS] at hn1
  have hs0 : s0 = 0 := by simp at hn1; omega
  subst hs0
  simp only [List.map_cons, List.map_nil, hw, List.cons.injEq, and_true] at hx1
  cases hx1
  rw [hB0, Option.some.injEq] at hB
  subst hB
  have la : (armsOf (lnorm ra)).length = (armsOf ra).length := by rw [armsOf_lnorm, List.length_map]
  simp only [Nat.sub_zero, Nat.zero_add, la, isBoxed_lnorm, shp_lnorm] at hA hB'
  
  have hsg2 : Ty.sum (sig ra) (sig rb) = Ty.sum (sig (cl ρ η.wit 0 0 u)) (sig (cl ρ η.wit 0 0 v)) := hsg
  simp only [Ty.sum.injEq] at hsg2
  have hs := hl.2.1
  simp only [close, substTs, skel, etok, Ty.sum.injEq] at hs
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨-, -, -, -, hly⟩ := hl
  simp only [close, substTs, lyt, etok, Ty.sum.injEq] at hly
  have layB : ∀ (ty : Ty) (t : Ty), isBoxed ty = true → etok (skel ty) = etok (skel (close th.σs t)) →
      etok (lyt 0 ty) = etok (lyt 0 (close th.σs t)) → ∀ pw, Lay th.σs t ty [pw] := by
    intro ty t hty hk hy pw
    refine ⟨fun us hu => ?_, hk, by rw [wc_isBoxed ty hty]; simp, Valid_boxed ty _ hty, hy⟩
    have h1 := wc_isBoxed ty hty
    simp only [wc, hu, Option.map_some, Option.some.injEq] at h1
    simp [h1]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := .sum ra rb) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have hlen : ∀ p1 : List Word, WLe B0.pay p1 → p1.length = nWords us := fun p1 h => h.length.symm.trans hnw.symm
  by_cases hj : B0.tag < (armsOf ra).length
  · have hArm : ∀ s1 p1, MemInvB g (CE η) s1 → WLe B0.pay p1 →
        injM g s1 ra B0.tag p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ra B0.tag p1,
          ThInvMFSBN p g (CE η) s1 th r2.1.mem r2.1.pairs (withS { th with term := e₁, env := (x, ra, r2.2) :: th.env } r2.1) := by
      intro s1 p1 hm1 hWp
      cases hty : isBoxed ra with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hA hj).2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ := case_arm_nbB hE.2.1 hty hsg2.1 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBSBN (hDy := hDy.leftW (fun _ => by rw [hterm]; rfl) rfl) (hRP1 := hRP1) hb1 he1 htv1 hi1 hE hm1 hty hq1 ⟨hs1, hsa, hw1, hv1, hly.1⟩ hvr1
      | true =>
          have harmA : (armsOf ra)[B0.tag]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_left hj]
          exact case_armBSBN (hDy := hDy.leftW (fun _ => by rw [hterm]; rfl) rfl) (hbf := hbf) (hRP1 := hRP1) (s0 := 0) hb1 he1 htv1 hi1 hE hm1 hn hty (by rw [harmA]; exact hus) (hlen p1 hWp)
            hw hB0 hsto0 hini0 (by omega) hWp ((hA hj).1 hty) (layB ra u hty hsa hly.1)
    simp only [PAx, tstep, hterm, hea] at hpx ⊢
    refine ⟨?_, fun r hr hpr0 => ?_⟩
    · rcases hpx with h0 | ⟨r, hr, -⟩
      rotate_left
      · exact List.ne_nil_of_mem hr
      obtain ⟨r1, h1, hp1⟩ := hne h0
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      intro hnil
      rw [List.flatMap_eq_nil_iff] at hnil
      have h2 := hnil _ h1
      simp only [hj, ite_true, List.map_eq_nil_iff] at h2
      exact (hArm s1 p1 hm1 hWp).1 h2
    · rw [List.mem_flatMap] at hr
      obtain ⟨r1, h1, hr⟩ := hr
      have hp1 : PromAbove r1.1 := by
        obtain ⟨f1, f2⟩ := (hpr r1 h1).1
        have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
        have hpa' := hpr0
        try simp only at hr
        split at hr
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      simp only [hj, ite_true, List.mem_map] at hr
      obtain ⟨r2, hr2, rfl⟩ := hr
      exact ThInvMFS_congrBN ((hArm s1 p1 hm1 hWp).2 r2 hr2) e5 e7 (congrArg Array.size e1) e4 e1
  · have hj' : (armsOf ra).length ≤ B0.tag := by omega
    have hArm : ∀ s1 p1, MemInvB g (CE η) s1 → WLe B0.pay p1 →
        injM g s1 rb (B0.tag - (armsOf ra).length) p1 ≠ [] ∧
          ∀ r2 ∈ injM g s1 rb (B0.tag - (armsOf ra).length) p1,
          ThInvMFSBN p g (CE η) s1 th r2.1.mem r2.1.pairs (withS { th with term := e₂, env := (y, rb, r2.2) :: th.env } r2.1) := by
      intro s1 p1 hm1 hWp
      cases hty : isBoxed rb with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hB' hj').2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ := case_arm_nbB hE.2.1 hty hsg2.2 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBSBN (hDy := hDy.rightW (fun _ => by rw [hterm]; rfl) rfl) (hRP1 := hRP1) hb2 he2 htv2 hi1 hE hm1 hty hq1 ⟨hs1, hsb, hw1, hv1, hly.2⟩ hvr1
      | true =>
          have harmB : (armsOf rb)[B0.tag - (armsOf ra).length]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_right hj']
          exact case_armBSBN (hDy := hDy.rightW (fun _ => by rw [hterm]; rfl) rfl) (hbf := hbf) (hRP1 := hRP1) (s0 := (armsOf ra).length) hb2 he2 htv2 hi1 hE hm1 hn hty
            (by rw [harmB]; exact hus) (hlen p1 hWp)
            hw hB0 hsto0 hini0 (by omega) hWp ((hB' hj').1 hty) (layB rb v hty hsb hly.2)
    simp only [PAx, tstep, hterm, hea] at hpx ⊢
    refine ⟨?_, fun r hr hpr0 => ?_⟩
    · rcases hpx with h0 | ⟨r, hr, -⟩
      rotate_left
      · exact List.ne_nil_of_mem hr
      obtain ⟨r1, h1, hp1⟩ := hne h0
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      intro hnil
      rw [List.flatMap_eq_nil_iff] at hnil
      have h2 := hnil _ h1
      simp only [hj, ite_false, List.map_eq_nil_iff] at h2
      exact (hArm s1 p1 hm1 hWp).1 h2
    · rw [List.mem_flatMap] at hr
      obtain ⟨r1, h1, hr⟩ := hr
      have hp1 : PromAbove r1.1 := by
        obtain ⟨f1, f2⟩ := (hpr r1 h1).1
        have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
        have hpa' := hpr0
        try simp only at hr
        split at hr
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      simp only [hj, ite_false, List.mem_map] at hr
      obtain ⟨r2, hr2, rfl⟩ := hr
      exact ThInvMFS_congrBN ((hArm s1 p1 hm1 hWp).2 r2 hr2) e5 e7 (congrArg Array.size e1) e4 e1
end
end TermStep.Flat

-- PORTB TermStep.lean:14266 tstepM_caseTS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_caseTSBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | case hu hb1 he1 hb2 he2 =>
    obtain ⟨u, v, c₁, c₂, c₃, hu, hb1, he1, hb2, he2⟩ : ∃ u v c₁ c₂ c₃,
        cx.use a = .ok (.sum u v, c₁) ∧ c₁.bind x u = .ok c₂ ∧ Typed p c₂ e₁ ∧
        c₁.bind y v = .ok c₃ ∧ Typed p c₃ e₂ := ⟨_, _, _, _, _, hu, hb1, he1, hb2, he2⟩
    obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · have htv12 := case_TvOK hu hb1 hb2 htv
      have ho : cx.opaqueOK _ = true :=
        peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have htb := (use_TvOK hu htv).2.1
      have hsg := lay_closed (ρ := ρ) hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl
      exact tstepM_caseBSBN (hDy := hDy) (hbf := hbf) (hRP1 := retPwN_eq hRP (use_ret hu)) hterm hn hb1 he1 htv12.1 hb2 he2 htv12.2 hi1 hea hv hl hS hsg hE hm hpx
    · refine paW <| tstepM_caseSBN (hDy := hDy) hterm (fun t' c₁' hu' => ?_) hT hi hE htv hm hRP hPS
      rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
      rw [← tier_of_eskel hl.2.1]; exact hS
end
end TermStep.Flat

-- PORTB TermStep.lean:14296 tstepM_caseT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_caseTBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  (tstepM_caseTSBN (hDy := hDy) (hRP := hRP) (hPS := hPS) (hterm := hterm) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hbf := hbf) (hpx := hpx)).imp id
    fun h r hr hp => (h r hr hp).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:17627 tstepM_loadWordOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadWordOwnBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P)))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hro), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨vcons n ρ, η, c', rfl, hE, he, htv', bind_FInvB hb (push_FInvB x n hi) hvr' (Lay_int w rfl), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:17671 tstepM_loadWordPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadWordPubBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P)))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk
      (by simp [Cx.opaqueOK, Ty.guardT]) hi hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨vcons n ρ, η, c', rfl, hE, he, htv', bind_FInvB hb (push_FInvB x n hi) hvr' (Lay_int w rfl), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:17729 storeWordOwn_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem storeWordOwn_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P))) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hj : IntIdx c₁ v j) (hst : InState c₁ P j c₂ k')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hj
  obtain ⟨rt, w, hev, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us0, -, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  have hpwf : pwf P = true := by
    obtain ⟨_, hvr0, -⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
  have hlen : [w].length = nWords [Acc.one] := rfl
  have husA : accs c.ty = some [Acc.one] := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords [Acc.one]) := by
    rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.one] [w] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩,
    MemInv_storeB hm hsto hown husA hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:18865 storeWordPub_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem storeWordPub_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P))) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hj : IntIdx c₁ v j) (hst : InState c₁ P j c₂ k')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hj
  obtain ⟨rt, w, hev, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hpwf : pwf P = true := by
    obtain ⟨ru0, pw0, lab0, us0, -, -, -, -, hne, hld, hstw⟩ :=
      loadPub_coreB (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi hpk htv ho
  obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
  have hlr : accs (Ty.word r'' P) = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  have husc : accs c.ty = some [.one] := by rw [← hlr, hus]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
  have hlen : [w].length = nWords [Acc.one] := rfl
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.one] [w] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  refine ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩, ?_⟩
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeFB hm hsto hown husc hval hlen s' hs'
  · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
    exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
      (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs'
end
end TermStep.Flat

-- PORTB TermStep.lean:18915 tstepM_storeWord
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact storeWordOwn_coreBN (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
    · exact storeWordPub_coreBN (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact storeWordOwn_coreBN (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
    · exact storeWordPub_coreBN (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact storeWordOwn_coreBN (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩ hi hE htv hm hRP
    · exact storeWordPub_coreBN (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:19072 tstepM_fence
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_fenceBN {x : String} {f : Fence} {e : Expr}
    (hterm : th.term = .let_ x (.fence f) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fence hb =>
  have key : tstep g mem pairs th =
      [((fenceS (stOf mem pairs th) (toWFence f)).mem, (fenceS (stOf mem pairs th) (toWFence f)).pairs,
        withS { th with term := e, env := (x, .unit, []) :: th.env } (fenceS (stOf mem pairs th) (toWFence f)))] := by
    simp only [tstep, hterm, evalOp]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ η .unit (shp .unit) [] := by simp [VRF, VRb2]
  have hlay : Lay th.σs .unit .unit [] := by
    refine ⟨fun us h => ?_, rfl, by simp [wc, accs], by simp [Valid], rfl⟩
    simp [accs] at h; subst h; rfl
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb (FInv_fenceCxB f hi) hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_fenceGB _ hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19101 tstepM_null
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_nullBN {x : String} {μ : Mode} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.null μ τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | null hwf hb =>
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .ptrOpt μ (close th.σs τ), [cst .null]) :: th.env }
          (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ η (.ptrOpt μ τ) (shp (.ptrOpt μ (close th.σs τ))) [cst .null] := by simp only [VRF, VRb2]; exact Or.inl rfl
  have hlay : Lay th.σs (.ptrOpt μ τ) (.ptrOpt μ (close th.σs τ)) [cst .null] := by
    refine ⟨fun us h => ?_, ?_, by simp [wc, accs], by simp only [Valid]; exact Or.inl rfl, ?_⟩
    · simp [accs] at h; subst h; rfl
    · simp [close, substTs, skel]
    · simp [close, substTs, lyt]
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19141 tstepM_mkWord
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_mkWordBN {x rn : String} {P : Proto} {v tk : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkWord rn P v tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hng : P.ghost = false) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWordGhost _ _ _ _ _ _ _ hg => rw [hng] at hg; cases hg
  | mkWord _ hpwf hu _ hv hst _ _ _ hb =>
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hv
  obtain ⟨rt, w, hea, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .word (.lit 0) P, [w]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hng, hea]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r', (VRF False) ρ η (.word r' P) (shp (.word (.lit 0) P)) [w] := by
    intro r'
    simp only [VRF, VRb2]
    refine ⟨hpwf, fun _ => ?_⟩
    obtain ⟨cl', hcl', hent⟩ := hst
    exact ⟨_, by simp [hwv], _, cl', _, hcl', hent ρ hi1.1⟩
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 (hvr _) (Lay_word _ _ _ hng w), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19179 tstepM_zero
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_zeroBN {x : String} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.zero τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | zero hwf hsc hz hb =>
  have ho := bind_opaqueOK hb
  have haf := bind_arrFree hb
  have hr : ∀ k, τ.guardT k = false → k < th.σs.length := lt_of_guardT (tb_of_wf τ hwf) hi.2.2.2.2.1
  have hsig : sig (close th.σs τ) = sig (cl ρ η.wit 0 0 τ) := sig_WitL hi.2.2.2.1 ρ ho hr
  have hafT : (cl ρ η.wit 0 0 τ).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af τ 0 0 haf
  have hafR : (close th.σs τ).arrFree = true := by rw [← arrFree_sig, hsig, arrFree_sig]; exact hafT
  have hR := KindSound.zero_close cx.ke th.σs τ hi.2.2.2.2.2.1.2.1 hz
  obtain ⟨zs, hzs, -⟩ := zpB _ _ (Nat.lt_succ_self _) [] [] hafR knone_nil hR
  obtain ⟨hval, hwc⟩ := zero_valOfB hi.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.1 ρ ho hr haf hR hzs
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, close th.σs τ, zs.map cst) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hzs]; rfl
  rw [key]
  refine ⟨by simp, fun r hr' => ?_⟩
  simp only [List.mem_singleton] at hr'
  subst hr'
  obtain ⟨hvr0, hV0⟩ := ValOfB.env hval
  have hwcr : wc (close th.σs τ) = some zs.length := by rw [wc_of_sig hsig]; exact hwc
  have hvr : (VRF False) ρ η τ (shp (close th.σs τ)) (zs.map cst) := by
    rw [shp_of_sig hsig]
    exact (VR_closeB hE.2.1 ρ τ [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 τ)) _ (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).2 hvr0
  have hlay : Lay th.σs τ (close th.σs τ) (zs.map cst) := by
    refine ⟨fun us h => ?_, rfl, by simp [hwcr], Valid_of_sig hsig.symm hV0, rfl⟩
    simp [wc, h] at hwcr; simp; omega
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19245 tstepM_fold
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_foldBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.fold a τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fold hwf hu hfo hb =>
  rename_i c₁ t
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, close th.σs τ, wsv) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hev]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hW : ∀ k, Clo (η.wit k) := fun k => (hE.2.1 k).1
  have hsat : Sat c₁.facts ρ := hi1.1
  suffices h : (VRF False) ρ η τ (shp (close th.σs τ)) wsv ∧ Lay th.σs τ (close th.σs τ) wsv from
    ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 h.1 h.2, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
  cases hfo with
  | @ptr μ ν u s hme hte =>
      have hg := wf_mu_guard (Or.inl hwf)
      have hcl := cl_tyEq0 hte η.wit 0 (fun _ => hsat)
      simp only [VRF, VRb2] at hvv
      obtain ⟨ad, c, h1, h2, h3, h4, h5, h6⟩ := hvv
      refine ⟨⟨ad, c, h1, h2, h3, Fd_foldS hW hg h4 hcl, by cases hme <;> exact h5, h6⟩,
        fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
      · simp [close, substTs, accs] at h; subst h; exact single_len h1
      · simp only [close, substTs, Valid]; exact ⟨_, h1⟩
  | @ptrOpt μ ν u s hme hte =>
      have hg := wf_mu_guard (Or.inr (Or.inl hwf))
      have hcl := cl_tyEq0 hte η.wit 0 (fun _ => hsat)
      simp only [VRF, VRb2] at hvv
      rcases hvv with hn | ⟨ad, c, h1, h2, h3, h4, h5, h6⟩
      · refine ⟨Or.inl hn, fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len hn
        · simp only [close, substTs, Valid]; exact Or.inl hn
      · refine ⟨Or.inr ⟨ad, c, h1, h2, h3, Fd_foldS hW hg h4 hcl, by cases hme <;> exact h5, h6⟩,
          fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len h1
        · simp only [close, substTs, Valid]; exact Or.inr ⟨_, h1⟩
  | @loc μ ν u s hme hte =>
      have hg := wf_mu_guard (Or.inr (Or.inr hwf))
      have hcl := cl_tyEq0 hte η.wit 0 (fun _ => hsat)
      simp only [VRF, VRb2] at hvv
      rcases hvv with ⟨hn, e0, he0⟩ | ⟨ad, c, U, h1, h3, h4, hF, h5, h6⟩
      · refine ⟨Or.inl ⟨hn, e0, Fd_foldS hW hg he0 hcl⟩, fun us h => ?_, rfl,
          by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len hn
        · simp only [close, substTs, Valid]; exact Or.inl hn
      · refine ⟨Or.inr ⟨ad, c, U, h1, h3, h4, Fd_foldS hW hg hF hcl, by cases hme <;> exact h5,
            by rw [← modeIni_meq hme]; exact h6⟩, fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len h1
        · simp only [close, substTs, Valid]; exact Or.inr ⟨_, h1⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19406 tstepM_ldlw
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_ldlwBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl : At} {e : Expr}
    (hterm : th.term = .let_ x (.ldlw b wi jl) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk hpj hij hb =>
  obtain ⟨t, u, n, k, jw, tj, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩ : ∃ t u n k jw tj q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi.2.1 hpj hoj
  have hJ := hlt ρ hi.1
  have hJk := hltk ρ hi.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).filterMap fun (s1, old) =>
        (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (m % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hni, hnj, addrOf, hwv, hbe, lanesOf]
  
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_filterMap.2 ⟨r0, hr0,
      (?_ : _ = some (r0.1, Ty.fix sg w, [cst (.num (laneN w y0 (m % w.lanes)))]))⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 ⊢; rw [hy0]; rfl
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv',
    bind_FInvB hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19493 tstepM_ldl
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_ldlBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.ldl b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk hb =>
  obtain ⟨t, u, n, k, j, q, hp, hbuf, hlo, hint, hlt, hltk, hb⟩ : ∃ t u n k j q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧ cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb hlt hltk
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).filterMap
        fun (s1, old) => (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (ev ρ j % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hni, addrOf, hwv, hbe, lanesOf]
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_filterMap.2 ⟨r0, hr0,
      (?_ : _ = some (r0.1, Ty.fix sg w, [cst (.num (laneN w y0 (ev ρ j % w.lanes)))]))⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 ⊢; rw [hy0]; rfl
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv',
    bind_FInvB hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19585 tstepM_stlw
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_stlwBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stlw b wi jl v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk hpj hij hpv hfx hb =>
  obtain ⟨t, u, n, k, jw, tj, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩ :
      ∃ t u n k jw tj tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi.2.1 hpj hoj
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ := hlt ρ hi.1
  have hJk := hltk ρ hi.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ jw)) false [.one]
            [cst (.num (setLaneN w y (m % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hev, hni, hnj, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw)
      (a := offs ad (ev ρ jw)) (rel := false) [.one] [cst (.num (setLaneN w y0 (m % w.lanes) yv))] 0 r0.1
      (by simp [nWords, Acc.size])
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, (?_ : (s2, Ty.unit, ([] : List Word)) ∈ _)⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 hs2 ⊢; rw [hy0]; exact List.mem_map_of_mem hs2
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ jw)) (hm1 (s1, old) h1 (storeUnits_promAbove hs2 hpr)) hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19690 tstepM_stl
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_stlBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stl b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stl hp hbuf hlo hint hlt hltk hpv hfx hb =>
  obtain ⟨t, u, n, k, j, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩ : ∃ t u n k j tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0 hlt hltk
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one]
            [cst (.num (setLaneN w y (ev ρ j % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hni, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw)
      (a := offs ad (ev ρ j / w.lanes)) (rel := false) [.one] [cst (.num (setLaneN w y0 (ev ρ j % w.lanes) yv))] 0 r0.1
      (by simp [nWords, Acc.size])
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, (?_ : (s2, Ty.unit, ([] : List Word)) ∈ _)⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 hs2 ⊢; rw [hy0]; exact List.mem_map_of_mem hs2
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j / w.lanes)) (hm1 (s1, old) h1 (storeUnits_promAbove hs2 hpr)) hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20290 casWord_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casWord_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r i j k' : Idx} {P : Proto} {c₂ : Nat}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hie : IntIdx cx e i) (hj : IntIdx cx v j) (hst : InState cx P j c₂ k')
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPwN th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨te, hte, hio⟩ := hie
  obtain ⟨rte, ew, hee, -, -⟩ := atom_numB hi.2.1 hte hio
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
  obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := casWordCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ hg hst hnwv hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ⟨lab, 0⟩ (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, addrOf, hpw]; rfl
  rw [key] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb]
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb]
    obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20337 tstepM_casWord
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casWordBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r : Idx} {P : Proto}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp hnw => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | casShare hp hw _ hie hj _ _ hst _ _ _ _ hlend hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWord_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, LendCx_TvOK hlend htv, LendCx_FInvB hlend hi, retPwN_eq hRP (LendCx_ret hlend)⟩
      hfail hi hE htv hm hRP
  | casTake hp hw _ hie hj _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hi' := bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl)
    have htv' := (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1
    split at hok
    · exact casWord_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPwN_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
    · exact casWord_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPwN_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
  | casEpoch hp hw _ _ hie hj _ hst _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWord_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
        bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPwN_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:20492 casCell_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casCell_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c₂ : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u te tv : Ty}
    (hpk : cx.peek w = .ok (.ptr .pub u)) (hone : u.rawWords = some 1)
    (hpe : cx.peek e = .ok te) (hu : cx.use v = .ok (tv, c₁))
    (hsube : SubS c₁ te u) (hsubv : SubS c₁ tv u) (hb : c₁.bind t .unit = .ok c₂)
    (hok : Typed p c₂ ok) (hfail : Typed p c₁ fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    
    (hRP : RetPwN th.σs th.stack cx.ret) (hkey : ∀ pw ew nw b, evalAt th.env w = some (.ptr .pub b, [pw]) → (∃ r, evalAt th.env e = some (r, [ew])) →
        (∃ r, evalAt th.env v = some (r, [nw])) → ∀ lab, pw.val = .loc ⟨lab, 0⟩ 0 →
      tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ⟨lab, 0⟩ (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩)) (hterm : th.term = .cas acq rel w e v t ok fail) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have htv1 := (use_TvOK hu htv).1
  have hlr : accs ru = accs (cl ρ η.wit 0 0 u) :=
    pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  have hus : accs ru = some [.one] := by rw [hlr]; exact accs_cl_one hone
  have husc : accs c.ty = some [.one] := by rw [(Fd_lay hcty).2.2.1]; exact accs_cl_one hone
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsubv ho htb hvv hlv hsig hus
  obtain ⟨nw, rfl⟩ := len_one hlen
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  obtain ⟨rte, wse, hee, hve, hle⟩ := peek_VRB (bkG := False) hi.2.1 hpe
  obtain ⟨-, hlene⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsube ho htb hve hle hsig hus
  obtain ⟨ew, rfl⟩ := len_one hlene
  obtain ⟨ru', pw', lab', us', hea', hpw', hus', -, hne, hld, hstw⟩ :=
    loadPub_coreB (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
  have e1 := Option.some.inj (hea.symm.trans hea')
  simp only [Prod.mk.injEq, List.cons.injEq, and_true, Ty.ptr.injEq, true_and] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain rfl : lab = lab' := by
    rw [hpw] at hpw'; simp only [Val.loc.injEq, WeakMem.Address.mk.injEq] at hpw'; exact hpw'.1.1
  obtain rfl : us' = [.one] := Option.some.inj (hus'.symm.trans hus)
  rw [hkey pw ew nw ru hea ⟨_, hee⟩ ⟨_, hev⟩ lab hpw] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨-, -, hm1⟩ := hld s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb']
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c₁, rfl, hE, hfail, htv1, hi1, retPwN_eq hRP (use_ret hu), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb']
    have hm2 : MemInvB g (CE η) s2 := by
      have hlen1 : [nw].length = nWords [Acc.one] := rfl
      have hm1' := MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
      by_cases hown : c.owner = some η.tid
      · exact MemInv_storeFB hm1' hsto hown husc hval hlen1 s2 hs2
      · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
        exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm1' hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
          (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen1 s2 hs2
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c₂, rfl, hE, hok, (bind_TvOK hb htv1 (by simp [tb]) (by simp [mg])).1,
      bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB hm2 (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20564 tstepM_casCell
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casCellBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u : Ty}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp _ hc hone _ hpe hu hsube hsubv _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨_, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
      subst hc
      exact casCell_coreBN (hterm := hterm) (hDy := hDy) hpk hone hpe hu hsube hsubv hb hok hfail hi hE htv hm hRP
        (fun pw ew nw b hea he hv lab hpw => by
          obtain ⟨_, hee⟩ := he
          obtain ⟨_, hev⟩ := hv
          simp only [tstep, hterm, hea, hee, hev, addrOf, hpw]; rfl)
    · simp [cellOf] at hc
  | casShare hp hw | casTake hp hw | casEpoch hp hw =>
    exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
end
end TermStep.Flat

-- PORTB TermStep.lean:20742 casWordLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casWordLoc_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r i j k' : Idx} {P : Proto} {c₂ : Nat}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hie : IntIdx cx e i) (hj : IntIdx cx v j) (hst : InState cx P j c₂ k')
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPwN th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨te, hte, hio⟩ := hie
  obtain ⟨rte, ew, hee, -, -⟩ := atom_numB hi.2.1 hte hio
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := wordLocCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ hg hst hnwv hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, haddr]; rfl
  rw [key] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb]
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb]
    obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20786 tstepM_casWordLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casWordLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r : Idx} {P : Proto}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp hnw => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | casShare hp hw _ hie hj _ _ hst _ _ _ _ hlend hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWordLoc_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, LendCx_TvOK hlend htv, LendCx_FInvB hlend hi, retPwN_eq hRP (LendCx_ret hlend)⟩
      hfail hi hE htv hm hRP
  | casTake hp hw _ hie hj _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hi' := bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl)
    have htv' := (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1
    split at hok
    · exact casWordLoc_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPwN_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
    · exact casWordLoc_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPwN_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
  | casEpoch hp hw _ _ hie hj _ hst _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWordLoc_coreBN (hDy := hDy) hterm hpk hμ hg hie hj hst
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
        bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPwN_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:20820 casCellLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casCellLoc_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c₂ : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u te tv : Ty}
    (hpk : cx.peek w = .ok (.loc .pub u)) (hone : u.rawWords = some 1)
    (hpe : cx.peek e = .ok te) (hu : cx.use v = .ok (tv, c₁))
    (hsube : SubS c₁ te u) (hsubv : SubS c₁ tv u) (hb : c₁.bind t .unit = .ok c₂)
    (hok : Typed p c₂ ok) (hfail : Typed p c₁ fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hRP : RetPwN th.σs th.stack cx.ret) (hkey : ∀ pw ew nw ad rt, evalAt th.env w = some (rt, [pw]) → (∃ r, evalAt th.env e = some (r, [ew])) →
        (∃ r, evalAt th.env v = some (r, [nw])) → addrOf pw = some ad →
      tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩)) (hterm : th.term = .cas acq rel w e v t ok fail) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have htv1 := (use_TvOK hu htv).1
  have hus1 : accs (cl ρ η.wit 0 0 u) = some [.one] := accs_cl_one hone
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, -, hsig, hne, hld, hsto, hstw⟩ :=
    locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk (.inr rfl) ho hus1 hi hE htv hm
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsubv ho htb hvv hlv hsig hus
  obtain ⟨nw, rfl⟩ := len_one hlen
  obtain ⟨rte, wse, hee, hve, hle⟩ := peek_VRB (bkG := False) hi.2.1 hpe
  obtain ⟨-, hlene⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsube ho htb hve hle hsig hus
  obtain ⟨ew, rfl⟩ := len_one hlene
  rw [hkey pw ew nw ad _ hea ⟨_, hee⟩ ⟨_, hev⟩ haddr] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨-, -, hm1⟩ := hld s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb']
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c₁, rfl, hE, hfail, htv1, hi1, retPwN_eq hRP (use_ret hu), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb']
    have hm2 : MemInvB g (CE η) s2 :=
      hsto _ [nw] (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view))
        hval rfl s2 hs2
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c₂, rfl, hE, hok, (bind_TvOK hb htv1 (by simp [tb]) (by simp [mg])).1,
      bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB hm2 (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20874 tstepM_casCellLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casCellLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u : Ty}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp _ hc hone _ hpe hu hsube hsubv _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨_, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
      subst hc
      exact casCellLoc_coreBN (hterm := hterm) (hDy := hDy) hpk hone hpe hu hsube hsubv hb hok hfail hi hE htv hm hRP
        (fun pw ew nw ad rt hea he hv haddr => by
          obtain ⟨_, hee⟩ := he
          obtain ⟨_, hev⟩ := hv
          simp only [tstep, hterm, hea, hee, hev, haddr]; rfl)
    · simp [cellOf] at hc
  | casShare hp hw | casTake hp hw | casEpoch hp hw =>
    exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
end
end TermStep.Flat

-- PORTB TermStep.lean:20901 tstepM_loadWordLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadWordLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  have hg' : P.ghost = false := hg
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg']
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, hne, hld, -, hstw⟩ :=
    locCellB (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ
      (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, haddr, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg' hvr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨vcons n ρ, η, c', rfl, hE, he, htv', bind_FInvB hb (push_FInvB x n hi) hvr' (Lay_int w rfl), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20941 storeWordLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem storeWordLoc_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hj : IntIdx c₁ v j) (hst : InState c₁ P j c₂ k')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hj
  obtain ⟨rt, w, hev, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, hne, hld, hsto, hstw⟩ :=
    locCellB (acq := false) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
      (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
  have hpwf : pwf P = true := by
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  have hval := storeWord_valB (η := η) (r := r) hpwf hi1.1 hst hwv
  have hlen : [w].length = nWords [Acc.one] := rfl
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, haddr, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    [.one] [w] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩,
    hsto _ [w] hm hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20979 tstepM_storeWordLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact storeWordLoc_coreBN (hDy := hDy) hterm hpk hμ hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact storeWordLoc_coreBN (hDy := hDy) hterm hpk hμ hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact storeWordLoc_coreBN (hDy := hDy) hterm hpk hμ hg hu hj hst hb he htv' ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:21033 tstepM_mkWordGhost
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_mkWordGhostBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : Proto} {v tk : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkWord rn P v tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hg : P.ghost = true) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord _ _ _ _ _ _ _ hng _ _ => rw [hg] at hng; cases hng
  | mkWordGhost _ hpwf hu _ _ _ _ _ _ hb =>
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .prod (.word (.lit 0) P) (.tok (.lit 0) none), []) :: th.env }
          (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hg]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r' j', (VRF False) ρ η (.prod (.word r' P) (.tok r' (some (P, j'))))
      (shp (.prod (.word (.lit 0) P) (.tok (.lit 0) none))) [] := by
    intro r' j'
    simp [VRF, VRb2, shp, hpwf, hg, wc, accs, Shp.wc, nWords]
  have hl2 := fun r' j' => Lay_pair (Lay_wordGhost th.σs r' P hg) (Lay_tokGhost th.σs r' P j')
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 (hvr _ _) (hl2 _ _), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21068 ghostRef
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ghostRefBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {t : Ty} {μ : Mode} {r : Idx} {P : Proto}
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = true)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) :
    ∃ rt pw b μ' ru, evalAt th.env a = some (rt, [pw]) ∧ cellOf rt = some (μ', ru) ∧
      addrOf pw = some b ∧ accs ru = some [] := by
  rcases ht with rfl | rfl
  · rcases hμ with rfl | rfl
    · obtain ⟨lab, c, pw, ru, hea, hpw, -, -, -, -, hsku, -⟩ :=
        ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
      obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
      exact ⟨_, pw, ⟨lab, 0⟩, _, _, hea, rfl, by simp [addrOf, hpw], by simp [accs, hg]⟩
    · obtain ⟨lab, c, pw, ru, f, hea, hpw, -, -, -, -, -, hsku, -⟩ :=
        pubPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
      obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
      exact ⟨_, pw, ⟨lab, 0⟩, _, _, hea, rfl, by simp [addrOf, hpw], by simp [accs, hg]⟩
  · obtain ⟨ad, pw, μr, ru, hea, haddr, hus, -⟩ := locCellB (acq := false) (rel := false) (us := [])
      hpk hμ (by simp [Cx.opaqueOK, Ty.guardT]) (by simp [cl, accs, hg]) hi hE htv hm
    exact ⟨_, pw, ad, _, _, hea, rfl, haddr, hus⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21093 tstepM_storeWordGhost
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordGhostBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = true)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨rt, pw, b, μ', ru, hea, hc, hab, hus⟩ := ghostRefBN hpk ht hμ hg hi hE htv hm
  have hnw : wordOf t ≠ none := by rcases ht with rfl | rfl <;> simp [wordOf]
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  have fin : ∀ {c₁ : Cx} {xt : Ty} {j : Idx}, FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c₁ th.env →
      IntIdx c₁ v j → c₁.bind x xt = .ok c' → StoreBindB ρ η th.σs xt →
      tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
    intro c₁ xt j hi1 hj hb htag
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.2.1 htvk hio
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .unit, []) :: th.env } (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hea, hev, hc, hab, hus, storeUnits, List.map]
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
  cases hop with
  | storeOwn hp hnw' | storePub hp hnw' | storeRgn hp hnw' | storeCap hp hnw' =>
    exfalso; rw [hpk] at hp; cases hp; exact hnw hnw'
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    exact fin (use_FInvB (bkG := False) hu hi).1 hj hb ⟨unit_VRB (bkG := False), unit_Lay _⟩
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    exact fin (use_FInvB (bkG := False) hu hi).1 hj hb ⟨unit_VRB (bkG := False), unit_Lay _⟩
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    exact fin (use_FInvB (bkG := False) hu hi).1 hj hb ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21193 tstepM_storeWordAny
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordAnyBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  cases hg : P.ghost
  · rcases ht with rfl | rfl
    · exact tstepM_storeWordBN (hDy := hDy) hterm hP hpk hμ hg hT hi hE htv hm hRP
    · exact tstepM_storeWordLocBN (hDy := hDy) hterm hP hpk hμ hg hT hi hE htv hm hRP
  · exact tstepM_storeWordGhostBN (hDy := hDy) hterm hP hpk ht hμ hg hT hi hE htv hm hRP hPS
end
end TermStep.Flat

-- PORTB TermStep.lean:21238 tstepM_mkWord2
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_mkWord2BN {x rn : String} {P : Proto2} {v0 v1 tk : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkWord2 rn P v0 v1 tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord2 _ hpwf hu _ hv0 hv1 hst _ _ hb =>
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .word2 (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r', (VRF False) ρ η (.word2 r' P) (shp (.word2 (.lit 0) P)) [w0, w1] := by
    intro r'
    simp only [VRF, VRb2]
    refine ⟨hpwf, _, _, by simp [hwv0, hwv1]; exact ⟨rfl, rfl⟩, ?_⟩
    obtain ⟨cl', hcl', hent⟩ := hst
    obtain ⟨h0, h1, h2⟩ := hent ρ hi1.1
    exact ⟨_, cl', _, _, hcl', h0, h1, h2⟩
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 (hvr _) (Lay_word2 _ _ _ w0 w1), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21274 tstepM_mkEPair
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_mkEPairBN {x rn : String} {P : ECounter} {v0 v1 : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkEPair rn P v0 v1) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkEPair _ hpwf hv0 hv1 hb =>
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_numB hi.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_numB hi.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .epair (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r', (VRF False) ρ η (.epair r' P) (shp (.epair (.lit 0) P)) [w0, w1] := by
    intro r'
    simp only [VRF, VRb2]
    exact ⟨hpwf, _, _, by simp [hwv0, hwv1]; exact ⟨rfl, rfl⟩⟩
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi (hvr _) (Lay_epair _ _ _ w0 w1), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21350 tstepM_ldpOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ldpOwnBN {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv hoq
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl hoq hea rfl)
  obtain ⟨hru, hpr⟩ := pair_ru .own hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hro), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨vcons m1 (vcons m0 ρ), η, c', rfl, hE, he, htv',
    bind_FInvB hb (push_FInvB n1 m1 (push_FInvB n0 m0 hi)) hvr' (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl)), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21393 tstepM_ldpPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ldpPubBN {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .pub u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk hoq hi hE htv hm
  obtain ⟨hru, hpr⟩ := pair_ru .pub hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨vcons m1 (vcons m0 ρ), η, c', rfl, hE, he, htv',
    bind_FInvB hb (push_FInvB n1 m1 (push_FInvB n0 m0 hi)) hvr' (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl)), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21444 stpOwn_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem stpOwn_coreBN {x : String} {rel : Bool} {a v0 v1 tk : At} {c₁ c' : Cx}
    {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.ptr .own (.word2 r P)))
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hj0 : IntIdx c₁ v0 j0) (hj1 : IntIdx c₁ v1 j1)
    (hst : InState2 c₁ P j0 j1 c₂ k0' k1')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hj0
  obtain ⟨tv1, htvk1, hio1⟩ := hj1
  obtain ⟨rt0, w0, hev0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hev1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us0, -, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  have hpwf : pwf2 P = true := by
    obtain ⟨_, hvr0, -⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word2 r'' P) = some [.two] := by simp [accs]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
  have hlen : [w0, w1].length = nWords [Acc.two] := rfl
  have husA : accs c.ty = some [Acc.two] := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords [Acc.two]) := by
    rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.two] [w0, w1] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩,
    MemInv_storeB hm hsto hown husA hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21493 stpPub_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem stpPub_coreBN {x : String} {rel : Bool} {a v0 v1 tk : At} {c₁ c' : Cx}
    {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.ptr .pub (.word2 r P)))
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hj0 : IntIdx c₁ v0 j0) (hj1 : IntIdx c₁ v1 j1)
    (hst : InState2 c₁ P j0 j1 c₂ k0' k1')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hj0
  obtain ⟨tv1, htvk1, hio1⟩ := hj1
  obtain ⟨rt0, w0, hev0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hev1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  have ho : cx.opaqueOK (.word2 r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hpwf : pwf2 P = true := by
    obtain ⟨ru0, pw0, lab0, us0, -, -, -, -, hne, hld, hstw⟩ :=
      loadPub_coreB (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi hpk htv ho
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word2 r'' P) = some [.two] := by simp [accs]
  have hlr : accs (Ty.word2 r'' P) = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  have husc : accs c.ty = some [.two] := by rw [← hlr, hus]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
  have hlen : [w0, w1].length = nWords [Acc.two] := rfl
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.two] [w0, w1] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  refine ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩, ?_⟩
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeFB hm hsto hown husc hval hlen s' hs'
  · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
    exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
      (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs'
end
end TermStep.Flat

-- PORTB TermStep.lean:21544 tstepM_stp
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_stpBN {x : String} {rel : Bool} {a v0 v1 tk : At} {μ : Mode} {r : Idx} {P : Proto2}
    {e : Expr}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | stpGive hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact stpOwn_coreBN (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
    · exact stpPub_coreBN (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | stpKeep hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact stpOwn_coreBN (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨by simp [VRF, VRb2], Lay_etok_unit rfl⟩ hi hE htv hm hRP
    · exact stpPub_coreBN (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨by simp [VRF, VRb2], Lay_etok_unit rfl⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:22092 casp_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem casp_coreBN {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {tw : Ty} {i0 i1 j0 j1 : Idx}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ tw)) (hμ : μ = .own ∨ μ = .pub)
    (htw : (∃ r P, tw = .word2 r P) ∨ (∃ r P, tw = .epair r P))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hnv : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      (∃ R ws, (VRF False) ρ η tw R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 tw) [n0, n1])
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPwN th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨te0, hte0, hio0⟩ := hie0
  obtain ⟨rt0, x0, hee0, -, -⟩ := atom_numB hi.2.1 hte0 hio0
  obtain ⟨te1, hte1, hio1⟩ := hie1
  obtain ⟨rt1, x1, hee1, -, -⟩ := atom_numB hi.2.1 hte1 hio1
  obtain ⟨tv0, htv0, hjo0⟩ := hj0
  obtain ⟨rtv0, n0, hev0, hn0, -⟩ := atom_numB hi.2.1 htv0 hjo0
  obtain ⟨tv1, htv1, hjo1⟩ := hj1
  obtain ⟨rtv1, n1, hev1, hn1, -⟩ := atom_numB hi.2.1 htv1 hjo1
  obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := caspCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ htw (hnv n0 n1 hn0 hn1) hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmwPair g.arch mem pairs (mth (stOf mem pairs th) pw n0 n1) 1 2 ⟨lab, 0⟩ x0.val x1.val
          (dataE 1 n0) (dataE 2 n1) [0] acq rel).map fun (mem', pairs', th') =>
        (mem', pairs', withS (if (th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1, th'.regs 2]⟩) := by
    simp only [tstep, hterm, hea, hee0, hee1, hev0, hev1, addrOf, hpw]; rfl
  rw [key] at ⊢
  obtain ⟨hx0, hx1⟩ := loadUnits_two_msg hne
  refine ⟨fun h => stepRmwPair_ne_nil hx0 hx1 (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd0, rd1, hl1, hr0, hr1, hcase⟩ := stepRmwPair_split (k := g.k) (s := stOf mem pairs th) hin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmc⟩ := stepRmwPair_mem hin (by decide) (MemInv_nopairB hm)
  have hp3 : th'.promises = th.promises := by
    rcases hmc with ⟨_, _, h⟩ | ⟨_, _, _, _, h, _⟩ <;> exact h
  have hs1p : s1.promises = th.promises :=
    (TermMem.loadUnits_frame [.two] 0 (stOf mem pairs th) (s1, [rd0, rd1]) hl1).2.2.1
  obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
  rcases hcase with ⟨hne', hsame⟩ | ⟨h0, h1, s2, hs2, hsame⟩ | ⟨h0, h1, tw', pm, htw', hpm, hpl, hsame⟩
  rotate_right
  · exfalso
    have e := hsame.2.2.2.1
    rw [lockS_prom] at e
    simp only [pairFulS] at e
    rw [hp3, hs1p] at e
    rw [hs1p] at htw'
    have hl := congrArg List.length e
    have h1 := List.length_erase_of_mem htw'
    have h2 := List.length_erase_le (l := th.promises.erase tw') (a := tw' + 1)
    have h3 := List.length_pos_of_mem htw'
    omega
  · have hp1 : PromAbove s1 := PromAbove_lockS (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 hp1
    have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = false := by
      rw [hr0, hr1]
      cases e0 : (rd0.val == x0.val) <;> cases e1 : (rd1.val == x1.val) <;> simp_all
    simp only [hb]
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = true := by
      rw [hr0, hr1]; simp [h0, h1]
    simp only [hb]
    have hp2 : PromAbove s2 :=
      PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 (fun t ht m hm => (storeUnits_promAbove (s := bumpRel (lockR g.arch (stOf mem pairs th) s1) _) hs2 hp2) t ht m hm)
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22170 tstepM_casp
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_caspBN {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {u : Ty}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  have hw2 : ∀ {r : Idx} {P : Proto2} {j0 j1 k0' k1' : Idx} {c₂ : Nat},
      u = .word2 r P → InState2 cx P j0 j1 c₂ k0' k1' →
      ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
        (∃ R ws, (VRF False) ρ η u R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 u) [n0, n1] := by
    intro r P j0 j1 k0' k1' c₂ hu' hst n0 n1 hn0 hn1 ⟨R, ws, hvr⟩
    subst hu'
    have hpwf : pwf2 P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeWord2_valB hpwf hi.1 hst hn0 hn1
  cases hT0 with
  | caspE hp hwn hwe _ hie0 hie1 hj0 hj1 _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp [word2Of] at hwn
    simp only [epairOf, Option.some.injEq, Prod.mk.injEq] at hwe; obtain ⟨rfl, rfl⟩ := hwe
    refine casp_coreBN (hDy := hDy) hterm hpk hμ (Or.inr ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1
      (fun n0 n1 hn0 hn1 ⟨R, ws, hvr⟩ => ?_)
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPwN_eq hRP (bind_ret hb)⟩
      hfail hi hE htv hm hRP
    have hpwf : pwfE P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeEPair_valB hpwf ⟨_, _, hn0, hn1⟩
  | caspBump hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreBN (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPwN_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspMove hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreBN (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPwN_eq hRP (bind_ret hb)⟩
        hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspTake hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreBN (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPwN_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
end
end TermStep.Flat

-- PORTB TermStep.lean:22246 tstepM_ldpLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ldpLocBN {x w n0 n1 : String} {acq : Bool} {μ : Mode} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, -, hstw⟩ :=
    locCellB (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ hoq
      (pair_accs_cl hu) hi hE htv hm
  obtain ⟨-, hpr⟩ := pair_ru_loc μr hu hsku
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, haddr, ↓reduceIte, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨vcons m1 (vcons m0 ρ), η, c', rfl, hE, he, htv',
    bind_FInvB hb (push_FInvB n1 m1 (push_FInvB n0 m0 hi)) hvr' (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl)), retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22284 stpLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem stpLoc_coreBN {x : String} {rel : Bool} {a v0 v1 tk : At} {c₁ c' : Cx}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.loc μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hj0 : IntIdx c₁ v0 j0) (hj1 : IntIdx c₁ v1 j1)
    (hst : InState2 c₁ P j0 j1 c₂ k0' k1')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hj0
  obtain ⟨tv1, htvk1, hio1⟩ := hj1
  obtain ⟨rt0, w0, hev0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hev1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
    locCellB (acq := false) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
      (by simp [Cx.opaqueOK, Ty.guardT]) (pair_accs_cl (wit := η.wit) (Or.inl ⟨r, P, rfl⟩)) hi hE htv hm
  have hpwf : pwf2 P = true := by
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hval := storeWord2_valB (η := η) (r := r) hpwf hi1.1 hst hwv0 hwv1
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, haddr, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    [.two] [w0, w1] 0 (stOf mem pairs th) rfl
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPwN_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩, hsto _ _ hm hval rfl s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22322 tstepM_stpLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_stpLocBN {x : String} {rel : Bool} {a v0 v1 tk : At} {μ : Mode} {r : Idx} {P : Proto2}
    {e : Expr}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | stpGive hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact stpLoc_coreBN (hDy := hDy) hterm hpk hμ hu hj0 hj1 hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | stpKeep hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact stpLoc_coreBN (hDy := hDy) hterm hpk hμ hu hj0 hj1 hst hb he htv' ⟨by simp [VRF, VRb2], Lay_etok_unit rfl⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:22383 casp_coreLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem casp_coreLocBN {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {tw : Ty} {i0 i1 j0 j1 : Idx}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.loc μ tw)) (hμ : μ = .own ∨ μ = .pub)
    (htw : (∃ r P, tw = .word2 r P) ∨ (∃ r P, tw = .epair r P))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hnv : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      (∃ R ws, (VRF False) ρ η tw R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 tw) [n0, n1])
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPwN th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  obtain ⟨te0, hte0, hio0⟩ := hie0
  obtain ⟨rt0, x0, hee0, -, -⟩ := atom_numB hi.2.1 hte0 hio0
  obtain ⟨te1, hte1, hio1⟩ := hie1
  obtain ⟨rt1, x1, hee1, -, -⟩ := atom_numB hi.2.1 hte1 hio1
  obtain ⟨tv0, htv0, hjo0⟩ := hj0
  obtain ⟨rtv0, n0, hev0, hn0, -⟩ := atom_numB hi.2.1 htv0 hjo0
  obtain ⟨tv1, htv1, hjo1⟩ := hj1
  obtain ⟨rtv1, n1, hev1, hn1, -⟩ := atom_numB hi.2.1 htv1 hjo1
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := caspLocCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ htw (hnv n0 n1 hn0 hn1) hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmwPair g.arch mem pairs (mth (stOf mem pairs th) pw n0 n1) 1 2 ad x0.val x1.val
          (dataE 1 n0) (dataE 2 n1) [0] acq rel).map fun (mem', pairs', th') =>
        (mem', pairs', withS (if (th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1, th'.regs 2]⟩) := by
    simp only [tstep, hterm, hea, hee0, hee1, hev0, hev1, haddr]; rfl
  rw [key] at ⊢
  obtain ⟨hx0, hx1⟩ := loadUnits_two_msg hne
  refine ⟨fun h => stepRmwPair_ne_nil hx0 hx1 (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd0, rd1, hl1, hr0, hr1, hcase⟩ := stepRmwPair_split (k := g.k) (s := stOf mem pairs th) hin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmc⟩ := stepRmwPair_mem hin (by decide) (MemInv_nopairB hm)
  have hp3 : th'.promises = th.promises := by
    rcases hmc with ⟨_, _, h⟩ | ⟨_, _, _, _, h, _⟩ <;> exact h
  have hs1p : s1.promises = th.promises :=
    (TermMem.loadUnits_frame [.two] 0 (stOf mem pairs th) (s1, [rd0, rd1]) hl1).2.2.1
  obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
  rcases hcase with ⟨hne', hsame⟩ | ⟨h0, h1, s2, hs2, hsame⟩ | ⟨h0, h1, tw', pm, htw', hpm, hpl, hsame⟩
  rotate_right
  · exfalso
    have e := hsame.2.2.2.1
    rw [lockS_prom] at e
    simp only [pairFulS] at e
    rw [hp3, hs1p] at e
    rw [hs1p] at htw'
    have hl := congrArg List.length e
    have h1 := List.length_erase_of_mem htw'
    have h2 := List.length_erase_le (l := th.promises.erase tw') (a := tw' + 1)
    have h3 := List.length_pos_of_mem htw'
    omega
  · have hp1 : PromAbove s1 := PromAbove_lockS (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 hp1
    have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = false := by
      rw [hr0, hr1]
      cases e0 : (rd0.val == x0.val) <;> cases e1 : (rd1.val == x1.val) <;> simp_all
    simp only [hb]
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = true := by
      rw [hr0, hr1]; simp [h0, h1]
    simp only [hb]
    have hp2 : PromAbove s2 :=
      PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 (fun t ht m hm => (storeUnits_promAbove (s := bumpRel (lockR g.arch (stOf mem pairs th) s1) _) hs2 hp2) t ht m hm)
    exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22458 tstepM_caspLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_caspLocBN {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {u : Ty}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  have hw2 : ∀ {r : Idx} {P : Proto2} {j0 j1 k0' k1' : Idx} {c₂ : Nat},
      u = .word2 r P → InState2 cx P j0 j1 c₂ k0' k1' →
      ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
        (∃ R ws, (VRF False) ρ η u R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 u) [n0, n1] := by
    intro r P j0 j1 k0' k1' c₂ hu' hst n0 n1 hn0 hn1 ⟨R, ws, hvr⟩
    subst hu'
    have hpwf : pwf2 P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeWord2_valB hpwf hi.1 hst hn0 hn1
  cases hT0 with
  | caspE hp hwn hwe _ hie0 hie1 hj0 hj1 _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp [word2Of] at hwn
    simp only [epairOf, Option.some.injEq, Prod.mk.injEq] at hwe; obtain ⟨rfl, rfl⟩ := hwe
    refine casp_coreLocBN (hDy := hDy) hterm hpk hμ (Or.inr ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1
      (fun n0 n1 hn0 hn1 ⟨R, ws, hvr⟩ => ?_)
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPwN_eq hRP (bind_ret hb)⟩
      hfail hi hE htv hm hRP
    have hpwf : pwfE P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeEPair_valB hpwf ⟨_, _, hn0, hn1⟩
  | caspBump hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreLocBN (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPwN_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspMove hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreLocBN (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPwN_eq hRP (bind_ret hb)⟩
        hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspTake hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreLocBN (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPwN_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
end
end TermStep.Flat

-- PORTB TermStep.lean:22797 fetch_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem fetch_coreBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {ad : Address} {pw nw : Word} {rt rv : Ty} {dd : Nat}
    {Q : List Word → Prop} {SOK : Word → Prop}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hea : evalAt th.env a = some (rt, [pw])) (haddr : addrOf pw = some ad)
    (hev : evalAt th.env v = some (rv, [nw])) (hnw : nw.val = .num dd)
    (hne : loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) ≠ [])
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) → PromAbove s1 →
      MemInvB g (CE η) s1 ∧ Q ws ∧ ∀ s1', MemInvB g (CE η) s1' → ∀ w, SOK w →
        ∀ s2, s2 ∈ storeUnits g.k g.arch pw ad rel [.one] [w] 0 s1' → MemInvB g (CE η) s2)
    (hpost : ∀ rd, Q [rd] → SOK (cst (o.kind.apply rd.val (.num dd))) ∧
      ∃ ρ' cx', Typed p cx' e ∧ TvOK cx' ∧
        FInvB g.lbase g.n g.i ρ' η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx' ((x, fetchRtTy rt, [rd]) :: th.env) ∧ RetPwN th.σs th.stack cx'.ret)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) (hE : EnvOKB p η) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (x, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => stepRmw_ne_nil_any (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨hm1, hq, hst⟩ := hcell s1 [rd] hl1 hp1
  obtain ⟨hsok, ρ', cx', he', htv', hi', hrpk⟩ := hpost rd hq
  rw [hnw] at hs2
  subst hrd
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ', η, cx', rfl, hE, he', htv', hi', hrpk, hDy.letW hterm rfl⟩,
    MemInv_sameB (MemInv_lockSB g.arch
      (MemInv_setRelB (hst _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) _ hsok s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22882 tstepM_fetch
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_fetchBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨lab, pw, ru, hea, hpw, hnwr, hne, hcell⟩ :=
        pubIntCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInvB (bkG := False) hu hi
      have hvi := VR_subB (bkG := False) hi1.1 hsub _ _ hvv
      simp only [VRF, VRb2] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      have hrt : fetchRtTy (.ptr .pub ru) = .int := by
        cases ru <;> simp [fetchRtTy, wordOf]
        exact (hnwr _ _ rfl).elim
      refine fetch_coreBN (hDy := hDy) hterm hea (by simp [addrOf, hpw]) hev hnwv hne hcell (fun rd hq => ?_) hE
      obtain ⟨n, hn⟩ := hq
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
      obtain ⟨m, hm'⟩ := FetchOp.apply_num o n dd
      refine ⟨⟨m, by simp [cst, Promises.TVal.mk0, hn, hm']⟩, ρ, c', he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
      rw [hrt]
      exact bind_FInvB hb hi1 (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    obtain ⟨lab, pw, μ', r', hea, hpw, hne, hcell⟩ :=
      wordCellFB (bkG := False) (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    have hrt : fetchRtTy (.ptr μ' (.word r' P)) = fetchEpochTy r' P := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreBN (hDy := hDy) hterm hea (by simp [addrOf, hpw]) hev hnwv hne hcell (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + 1)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_epoch hpwf hep (n + 1)), ρ, c', he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (VR_fetchEpochB hn) (Lay_fetchEpoch _ r r' P rd)
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    obtain ⟨lab, pw, μ', r', hea, hpw, hne, hcell⟩ :=
      wordCellFB (bkG := False) (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    have hrt : fetchRtTy (.ptr μ' (.word r' P)) = .int := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreBN (hDy := hDy) hterm hea (by simp [addrOf, hpw]) hev hnwv hne hcell (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, hin⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + d)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_fetch hok hin), ρ, c', he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
end
end TermStep.Flat

-- PORTB TermStep.lean:22981 tstepM_fetchLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_fetchLocBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
      obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
        locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
          (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInvB (bkG := False) hu hi
      have hvi := VR_subB (bkG := False) hi1.1 hsub _ _ hvv
      simp only [VRF, VRb2] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      have hrt : fetchRtTy (.loc μr ru) = .int := by
        cases ru <;> simp [fetchRtTy, wordOf]
        simp [skel, etok, close, substTs] at hsku
      refine fetch_coreBN (hDy := hDy) (Q := fun ws => ∃ n, ws.map (·.val) = [.num n])
        (SOK := fun w => ∃ m, w.val = .num m) hterm hea haddr hev hnwv hne
        (fun s1 ws hl hp1 => ?_) (fun rd hq => ?_) hE
      · obtain ⟨hvr, -, hm1⟩ := hld s1 ws hl hp1
        refine ⟨hm1, by simpa [VRF, VRb2] using hvr, fun s1' hm1' w ⟨m, hw⟩ s2 hs2 => ?_⟩
        exact hsto s1' [w] hm1' (intValB (ρ := ρ) hw) rfl s2 hs2
      · obtain ⟨n, hn⟩ := hq
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
        obtain ⟨m, hm'⟩ := FetchOp.apply_num o n dd
        refine ⟨⟨m, by simp [cst, Promises.TVal.mk0, hn, hm']⟩, ρ, c', he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
        rw [hrt]
        exact bind_FInvB hb hi1 (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
      locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    have hrt : fetchRtTy (.loc μr (.word r' P)) = fetchEpochTy r' P := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreBN (hDy := hDy) (Q := fun ws => (VRF False) ρ η (.word r P) (shp (.word r' P)) ws)
      (SOK := fun w => EnvValB (CE η) (cl ρ η.wit 0 0 (.word r P)) [w]) hterm hea haddr hev hnwv hne
      (fun s1 ws hl hp1 => ⟨(hld s1 ws hl hp1).2.2, (hld s1 ws hl hp1).1,
        fun s1' hm1' w hw s2 hs2 => hsto s1' [w] hm1' hw rfl s2 hs2⟩) (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + 1)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_epoch hpwf hep (n + 1)), ρ, c', he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (VR_fetchEpochB hn) (Lay_fetchEpoch _ r r' P rd)
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
      locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    have hrt : fetchRtTy (.loc μr (.word r' P)) = .int := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreBN (hDy := hDy) (Q := fun ws => (VRF False) ρ η (.word r P) (shp (.word r' P)) ws)
      (SOK := fun w => EnvValB (CE η) (cl ρ η.wit 0 0 (.word r P)) [w]) hterm hea haddr hev hnwv hne
      (fun s1 ws hl hp1 => ⟨(hld s1 ws hl hp1).2.2, (hld s1 ws hl hp1).1,
        fun s1' hm1' w hw s2 hs2 => hsto s1' [w] hm1' hw rfl s2 hs2⟩) (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, hin⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + d)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_fetch hok hin), ρ, c', he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
end
end TermStep.Flat

-- PORTB TermStep.lean:23290 tstep_region
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_regionBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  have hx := Ext_bumpRB hE.2.1
  obtain ⟨c, hc, hvc, hk, ⟨μ, u, ws, hea, hf⟩ | ⟨μ, u, ψ, ws, hea, hf⟩⟩ := region_stepB hT hi htv (ridNext η)
  all_goals
    simp only [tstep, hterm, hea]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, bumpRB η, c, CE_bumpRB η, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, hc, hvc, FInv_extB hE.2.1 hx (by simpa [withS] using hf), retPwN_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:23307 tstep_openPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_openPubBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {rn pn cn : String} {e : Expr}
    (hterm : th.term = .openPub a rn pn cn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  have hx := Ext_bumpRB hE.2.1
  obtain ⟨c, hc, hvc, hk, μ, u, ws, hea, hf⟩ := openPub_stepB hT hi htv (ridNext η)
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨_, bumpRB η, c, CE_bumpRB η, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, hc, hvc, FInv_extB hE.2.1 hx (by simpa using hf), retPwN_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:33135 tstepM_region
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
variable {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_regionBN {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  ⟨(tstep_regionBN (hDy := hDy) hterm hT hi hE htv hRP hPS).1, fun r hr =>
    ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, (tstep_regionBN (hDy := hDy) hterm hT hi hE htv hRP hPS).2 r hr, by
      rw [fence_region hterm r hr]; exact MemInv_fenceGB _ hm⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:33143 tstepM_openPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
variable {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_openPubBN {a : At} {rn pn cn : String} {e : Expr}
    (hterm : th.term = .openPub a rn pn cn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 :=
  liftBN hm (tstep_openPubBN (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_openPub hterm)
end
end TermStep.Flat

-- ♭ mirror of W TermStep tstepM_isTy (ADD4 isTy op), resource-free layer.
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_isTyBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.isTy a τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret)
    (hPS : PwSkel) (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | isTy hpk hsl hwf htg _ hb =>
  obtain ⟨rt, ws, hea, hvr0, hlay0⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  obtain ⟨pw, ad, cl0, hlast, hpv, ho, hsto, hmo, hacc⟩ := slot_wordB hsl hvr0 hlay0.2.2.1
  obtain ⟨w, hw, hk⟩ := isTy_key (g := g) (mem := mem) (pairs := pairs) hterm hea hlast hpv (close_wf0 th.σs hwf)
  rw [hk]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ η (.ptrOpt .pub τ) (shp (.ptrOpt .pub (close th.σs τ))) [w] := by
    simp only [VRF, VRb2]; exact isTy_valB htg hTy hpv ho hsto hmo hacc hw
  exact ⟨CE η, ⟨EFoot_reflB, cntX_refl⟩, ⟨ρ, η, c', rfl, hE, he, htv', by
      simpa [withS] using bind_FInvB hb hi hvr (isTy_lay (isTy_null_or hpv hw)),
    retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:33244 tstepMF_step
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepMF_stepBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ThInvMFBN p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | spawn => exact False.elim hsc
    | ext => exact False.elim hsc
    | isTy => exact paW <| tstepM_isTyBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS hTy
    | atom | pair | addS | addI | subS | pack | rem | nameI | bits | bit1 | vmatch | band
    | cvt | toInt | asLanes | fop | fcmp | fop1 | lane | setLane =>
        exact paW <| tstepM_pureBN (hDy := hDy) ht trivial hP hT hi hE htv hm hRP hPS
    | packT => exact paW <| tstepM_pureBN (hDy := hDy) ht hsc hP hT hi hE htv hm hRP hPS
    | inl => exact tstepM_inlTBN (hDy := hDy) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP hPS
    | inr => exact tstepM_inrTBN (hDy := hDy) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP hPS
    | new => exact paW <| tstepM_newBN (hDy := hDy) ht hsc hP hn hT hi hE htv hm hRP hPS
    | publish | publishBuf =>
        exact paW <| (tstepM_publishBN (hDy := hDy) (hPb := hPb) ht hP hT hi hE htv hm hsc (fun rt ws ad => hwin _ _ _ rt ws ad ht) hRP hPS).imp
          id fun h r hr => (h r hr).toF
    | intoRgn | intoRgnBuf => exact False.elim hsc
    | newBuf => exact paW <| tstepM_newBufBN (hDy := hDy) ht hsc hP hn hT hi hE htv hm hRP hPS
    | idxOwn | idxShared => exact paW <| tstepM_idxBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | bufInit => exact tstepM_bufInitBN (hDy := hDy) ht hP hT hi hE htv hm hZ hRP hPS
    | null => exact paW <| tstepM_nullBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | fldOwn | fldShared => exact paW <| tstepM_fldBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | fence => exact paW <| tstepM_fenceBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | zero => exact paW <| tstepM_zeroBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | call => exact paW <| tstepM_callBN (hDy := hDy) hp hP ht hT hi hE htv hm hsc hRP
    | fnptr => exact paW <| tstepM_fnptrBN (hDy := hDy) hp hP ht hT hi hE htv hm hRP hPS
    | callc => exact paW <| tstepM_callcBN (hDy := hDy) hp hP ht hT hi hE htv hm hRP hSig
    | xchgAt => exact tstepM_xchgAtBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | loadAt => exact tstepM_loadAtBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | xchgAtF => exact tstepM_xchgAtFBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | loadAtF => exact tstepM_loadAtFBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | ldlw => exact tstepM_ldlwBN (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | ldl => exact tstepM_ldlBN (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | stlw => exact tstepM_stlwBN (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | stl => exact tstepM_stlBN (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | fold => exact paW <| tstepM_foldBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | mkWord _ _ _ _ _ _ _ hng _ _ => exact paW <| tstepM_mkWordBN (hDy := hDy) ht hP hT hi hE htv hm hng hRP hPS
    | mkWordGhost _ _ _ _ _ _ _ hg _ _ => exact paW <| tstepM_mkWordGhostBN (hDy := hDy) ht hP hT hi hE htv hm hg hRP hPS
    | validate | borrow | freeze | endBorrow =>
        exact False.elim hsc
    | mkWord2 => exact paW <| tstepM_mkWord2BN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | mkEPair => exact paW <| tstepM_mkEPairBN (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | ldp hpk =>
        obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hsc _ hpk
        · rw [hteq] at hpk
          rcases hμ with rfl | rfl
          · exact tstepM_ldpOwnBN (hDy := hDy) ht hP hu hpk hT hi hE htv hm hRP hPS
          · exact tstepM_ldpPubBN (hDy := hDy) ht hP hu hpk hT hi hE htv hm hRP hPS
        · rw [hteq] at hpk
          exact tstepM_ldpLocBN (hDy := hDy) ht hP hu hpk hμ hT hi hE htv hm hRP hPS
    | stpGive hpk | stpKeep hpk =>
        obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc _ hpk
        · rw [hteq] at hpk
          exact paW <| tstepM_stpBN (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP
        · rw [hteq] at hpk
          exact paW <| tstepM_stpLocBN (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP
    | mkTicket | claim => exact False.elim hsc
    | fetchCell hpk | fetchEpoch hpk | fetchShare hpk =>
        obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc _ hpk
        · rw [hteq] at hpk
          exact tstepM_fetchBN (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP hPS
        · rw [hteq] at hpk
          exact tstepM_fetchLocBN (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP hPS
    | loadWord hpk hw =>
        obtain ⟨μ, hteq | hteq⟩ := wordOf_cases hw <;> subst hteq
        · cases μ with
          | own => exact tstepM_loadWordOwnBN (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
          | pub => exact tstepM_loadWordPubBN (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
          | rgn r' => exact ((hsc _ hpk) r' _ rfl).elim
        · cases μ with
          | own => exact tstepM_loadWordLocBN (hDy := hDy) ht hP hpk (.inl rfl) hT hi hE htv hm hRP hPS
          | pub => exact tstepM_loadWordLocBN (hDy := hDy) ht hP hpk (.inr rfl) hT hi hE htv hm hRP hPS
          | rgn r' => exact ((hsc _ hpk) r' _ rfl).elim
    | storeWordGive hpk hw | storeWordKeep hpk hw | storeWordHand hpk hw =>
        obtain ⟨μ, hteq⟩ := wordOf_cases hw
        cases μ with
        | own => exact paW <| tstepM_storeWordAnyBN (hDy := hDy) ht hP hpk hteq (.inl rfl) hT hi hE htv hm hRP hPS
        | pub => exact paW <| tstepM_storeWordAnyBN (hDy := hDy) ht hP hpk hteq (.inr rfl) hT hi hE htv hm hRP hPS
        | rgn r' => rcases hteq with rfl | rfl <;> exact ((hsc _ hpk) r' _ rfl).elim
    | loadRgn hpk _ hc | loadCap hpk _ hc | loadTorn hpk _ hc => exact absurd hc (hsc _ hpk _ _)
    | storeRgn hpk _ hc | storeCap hpk _ hc => exact absurd hc (hsc _ hpk _ _)
    | loadOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact tstepM_loadOwnBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact tstepM_loadLocBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | loadPub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact tstepM_loadPubBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact tstepM_loadPubLocBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | storeOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact paW <| tstepM_storeOwnBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact paW <| tstepM_storeLocBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | storePub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact paW <| tstepM_storePubBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact paW <| tstepM_storePubLocBN (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | xchg hpk hx =>
        cases hx with
        | own _ hc =>
            rcases cell_cases hc with rfl | rfl
            · exact tstepM_xchgOwnBN (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
            · exact tstepM_xchgLocBN (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
        | rgn _ hc => exact absurd hc (hsc _ hpk _ _)
  | split => exact paW <| tstepM_splitBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | unpack => exact paW <| tstepM_unpackBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | unpackT => exact paW <| tstepM_unpackTBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | ifnull => exact paW <| tstepM_ifnullBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | parity => exact paW <| tstepM_parityBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | ifeqPlain | ifeq | ifeqRec | ifeqZero => exact paW <| tstepM_ifeqBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | case => exact tstepM_caseTBN (hDy := hDy) (hbf := hbf) ht hn hT hi hE htv hm hpx hRP hPS
  | region | regionBuf => exact paW <| tstepM_regionBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | openPub => exact paW <| tstepM_openPubBN (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | casCell hpk | casShare hpk | casTake hpk | casEpoch hpk =>
      rcases hsc _ hpk with ⟨μ, r, P, hteq, hμ⟩ | ⟨u, rfl | rfl, hnw⟩
      · cases hg : P.ghost
        · rcases hteq with rfl | rfl
          · exact tstepM_casWordBN (hDy := hDy) ht hpk hμ hg hT hi hE htv hm hRP
          · exact tstepM_casWordLocBN (hDy := hDy) ht hpk hμ hg hT hi hE htv hm hRP
        · exact (cas_ghost_absurd (by rw [← ht]; exact hT) hpk hteq
            (wordRef_pwfB hpk hteq hμ hi hE htv hm) hg).elim
      · exact tstepM_casCellBN (hDy := hDy) ht hpk hnw hT hi hE htv hm hRP
      · exact tstepM_casCellLocBN (hDy := hDy) ht hpk hnw hT hi hE htv hm hRP
  | caspMove hpk | caspTake hpk | caspE hpk | caspBump hpk =>
      obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hsc _ hpk
      · rw [hteq] at hpk
        exact tstepM_caspBN (hDy := hDy) ht hpk hμ hu hT hi hE htv hm hRP
      · rw [hteq] at hpk
        exact tstepM_caspLocBN (hDy := hDy) ht hpk hμ hu hT hi hE htv hm hRP
  | ret =>
      have hst : th.stack ≠ [] := by
        intro h; simp [isDone, ht, h] at hnd
      exact paW <| tstepM_retBN ht hst hT hi hE htv hm hn
  | tail => exact paW <| tstepM_tailBN (hDy := hDy) hp hP ht hT hi hE htv hm hsc hRP hPS hSub
end
end TermStep.Flat

-- PORTB TermPlantF.lean:1358 SWIni
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem SWIniBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {loc : Address} {val : WeakMem.Val}
    (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hsw : TermFul.SW g mem pairs th loc val) :
    (∃ c, η.sto loc.label = some c ∧ InitR η c loc.label loc.offset) ∨
      ∃ x bb i v e, th.term = .let_ x (.bufInit bb i v) e := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · have hT' := hT
    rw [hterm] at hT' hsc
    cases hT' with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, rfl, -⟩ |
            ⟨o, acq, rel, a, v, t, t', pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · rcases unitsOp_uaIB hop hsc hi hE htv hu with hU | ⟨bb, i, v, rfl⟩
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initR hU hj
            exact .inl ⟨c, hc, by simpa [offs] using hI⟩
          · exact .inr ⟨x, bb, i, v, e, hterm⟩
        · obtain ⟨c, hc, hI⟩ := unitsAtI_initR (fetch_swIB hop hsc hi hE htv hm hea hb) (.here _)
          exact .inl ⟨c, hc, by simpa using hI⟩
  · rw [hterm] at hT hsc
    obtain ⟨c, hc, hI⟩ := unitsAtI_initR (cas_swIB hT hsc hi hE htv hm hea hb) (.here _)
    exact .inl ⟨c, hc, by simpa using hI⟩
end
end TermPlantF.Flat

-- PORTB TermAnch.lean:108 wrSite_ok
namespace TermAnch.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wrSite_okBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hr : r ∈ tstep g mem pairs th) : WrSite g (CE η) mem pairs th r := by
  intro t m ht hmt
  by_cases hlt : t < mem.size
  · have hm0 : mem[t]? = some mem[t] := by simp [hlt]
    have e2 := (TermFul.tstep_grow hr).1 t _ hm0
    rw [hmt] at e2
    simp only [Option.some.injEq] at e2
    have hm1 : mem[t]? = some m := by rw [hm0, e2]
    by_cases htp : t ∈ th.promises
    · obtain ⟨m', hm', hsw, -, -⟩ :=
        (TermFul.tstep_fulfil (MemInv_promLtB hm) (MemInv_nopairB hm) hr).2 t htp ht
      have hm'' : mem[t]? = some m' := hm'
      rw [hm1] at hm''; cases hm''
      rcases TermPlantF.Flat.SWIniBN hE hT htv hi hm (TermTyped.scopeD_SW hsc hsw) hsw with h | ⟨x, bb, ib, v, e, hterm⟩
      · exact .inr (.inr (.inl h))
      · refine .inr (.inr (.inr ⟨x, bb, ib, v, e, hterm, ?_⟩))
        rcases hsw with ⟨x', op, e', hterm', hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hterm', -⟩
        · rw [hterm] at hterm'
          simp only [Expr.let_.injEq] at hterm'
          obtain ⟨rfl, rfl, rfl⟩ := hterm'
          rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop', -⟩
          · have hT' := hT
            rw [hterm] at hT'
            cases hT' with
            | let_ hop _ => rw [hl]; exact bufInit_siteB (η := η) hop hi hE htv hu (TermFul.OneAt_lt hj)
          · cases hop'
        · rw [hterm] at hterm'; cases hterm'
    · exact .inl ⟨htp, hm1⟩
  · rcases TermB5.tstep_newR (MemInv_promLtB hm) hr t m (by omega) hmt with hf | hn
    · exact .inr (.inl hf)
    rcases hn with ⟨x, op, e, hterm, b, us, j, hon, hl, hrole⟩ |
        ⟨acq, rel, w, e, v, tn, ok, fail, tw, pw, hterm, hea, hb⟩ |
        ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, tw, pw, A, hterm, hea, hb, hl⟩
    · have hjl := TermB5.roleR_lt hrole
      have hss : StepScope cx th.term := hsc.elim id fun h => (newR_cap h.2 hterm hon).elim
      rw [hterm] at hT hss
      cases hT with
      | let_ hop _ =>
          rcases hon with ⟨pw, rel, ws, hu⟩ | ⟨rel, a, v0, v1, tk, t', pw, rfl, hea, hb, rfl⟩ |
              ⟨o, acq, rel, a, v, t', pw, rfl, hea, hb, rfl⟩
          · rcases TermPlantF.Flat.unitsOp_uaIB hop hss hi hE htv hu with hU | ⟨bb, ib, v, rfl⟩
            · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hU hjl
              exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
            · refine .inr (.inr (.inr ⟨x, bb, ib, v, e, hterm, ?_⟩))
              rw [hl]; exact bufInit_siteB (η := η) hop hi hE htv hu hjl
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (stp_uaIPB hop hss hi hea hb) hjl
            exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (TermPlantF.Flat.fetch_swIB hop hss hi hE htv hm hea hb) hjl
            exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
    · have hss : StepScope cx th.term := hsc.elim id fun h => by
        obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := h.2 <;> rw [he] at hterm <;> cases hterm
      rw [hterm] at hT hss
      obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (TermPlantF.Flat.cas_swIB hT hss hi hE htv hm hea hb)
        (show 0 < nWords [Acc.one] by decide)
      have e0 : m.loc = offs m.loc 0 := (TermStepper.offs_zero _).symm
      exact .inr (.inr (.inl ⟨c, hc, by rw [e0]; exact hI⟩))
    · have hss : StepScope cx th.term := hsc.elim id fun h => by
        obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := h.2 <;> rw [he] at hterm <;> cases hterm
      rw [hterm] at hT hss
      have hua := casp_uaIPB hT hss hi hea hb
      rcases hl with ⟨hl, -⟩ | ⟨hl, -⟩
      · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hua (show 0 < nWords [Acc.two] by decide)
        have e0 : m.loc = offs A 0 := by rw [hl, TermStepper.offs_zero]
        exact .inr (.inr (.inl ⟨c, by rw [e0]; exact hc, by rw [e0]; exact hI⟩))
      · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hua (show 1 < nWords [Acc.two] by decide)
        have e0 : m.loc = offs A 1 := hl
        exact .inr (.inr (.inl ⟨c, by rw [e0]; exact hc, by rw [e0]; exact hI⟩))
end
end TermAnch.Flat

-- PORTB TermWrSiteA.lean:47 ful_x
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ful_xBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} {t : Nat} {m : Msg} (hE : EnvOKB p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hvr : TermSeenHid.EnvVR th) (hr : r ∈ tstep g mem pairs th)
    (htp : t ∈ th.promises) (htn : t ∉ r.2.2.promises) (hsw : TermFul.SW g mem pairs th m.loc m.val) :
    FulX η m.loc.label m.loc.offset t ∨ ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, hee, hev, hb, -⟩
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
      rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hloc, -⟩ |
          ⟨o, acq, rel, a', v, ty1, ty2, pw, nw, tr, mr, rfl, hea, hev, hb, -⟩
      · have hjl := TermFul.OneAt_lt hj
        rw [hloc]
        cases op
        case store rl a1 v1 tok =>
          have hsc' : OpScope cx (.store rl a1 v1 tok) := hsc
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := store_TIB hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact .inl (own_x hsto hus' hini hjl)
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
              intro F h1 h2
              have hr' := hr
              rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
              obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr'
              rw [← hreq] at htn
              simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_map] at hin
              obtain ⟨s'', hs'', he⟩ := hin
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, -, -⟩ := he
              exact htn (PVc.storeUnits_keepLow hs'' htp h1 h2)
            exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk (fun hb0 _ => own_x hsto hus' hb0 hjl))
        case xchg a1 v1 =>
          have hsc' : OpScope cx (.xchg a1 v1) := hsc
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := xchg_TIB hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact .inl (own_x hsto hus' hini hjl)
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
              intro F h1 h2
              have hr' := hr
              rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
              obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr'
              rw [← hreq] at htn
              simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_flatMap, List.mem_map] at hin
              obtain ⟨⟨s1, old⟩, hl, s'', hs'', he⟩ := hin
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, -, -⟩ := he
              have hk1 := (TermFul.loadUnits_keep us 0 _ _ hl).2.2
              have hh1 : t ∈ s1.promises := by rw [hk1]; exact htp
              exact htn (PVc.storeUnits_keepLow hs'' hh1 h1 h2)
            exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk (fun hb0 _ => own_x hsto hus' hb0 hjl))
        case xchgAt =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAt_uaRB hop hi hE htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case xchgAtF =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAtF_uaRB hop hi hE htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case stl =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stl_uaRB hop hi htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case stlw =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stlw_uaRB hop hi htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case bufInit bb i1 v1 =>
          exact .inr ⟨x, bb, i1, v1, e, hterm⟩
        all_goals simp [TermFul.UnitsOp] at hu
      · have hsc' : OpScope cx (.fetch o acq rel a' v) := hsc
        obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := fetch_TIB hop hsc' hi hE htv hm hea hb
        rcases hμ with rfl | rfl
        · exact .inl (add_zero_x (own_x (j := 0) hsto hus' hini (by decide)))
        · have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
            intro F h1 h2
            have hr' := hr
            rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
            obtain ⟨⟨s', t'', ws'⟩, hin, hreq⟩ := hr'
            rw [← hreq] at htn
            simp only [evalOp, hea, hev, hb, List.mem_map] at hin
            obtain ⟨⟨mem', th'⟩, hst, he⟩ := hin
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, -, -⟩ := he
            exact htn (PVc.stepRmw_keepLow hst htp h1 h2)
          exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk
            (fun hb0 _ => add_zero_x (own_x (j := 0) hsto hus' hb0 (by decide))))
  · rw [hterm] at hT hsc
    obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := cas_TIB hT hsc hi hE htv hm hea hb
    rcases hμ with rfl | rfl
    · exact .inl (add_zero_x (own_x (j := 0) hsto hus' hini (by decide)))
    · have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
        intro F h1 h2
        have hr' := hr
        simp only [tstep, hterm, hea, hee, hev, hb, List.mem_map] at hr'
        obtain ⟨⟨mem', th'⟩, hst, hreq⟩ := hr'
        rw [← hreq] at htn
        exact htn (PVc.stepRmw_keepLow (s := stOf mem pairs th) hst htp h1 h2)
      exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk
            (fun hb0 _ => add_zero_x (own_x (j := 0) hsto hus' hb0 (by decide))))
end
end TermWrSiteA.Flat

-- PORTB TermWrSiteA.lean:146 buf_x
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem buf_xBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {m : Msg} (hE : EnvOKB p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hsw : TermFul.SW g mem pairs th m.loc m.val) {x : String} {bb ib v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit bb ib v) e) :
    ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e ∧ ∃ rt w ad rti wi n c,
      evalAt th.env bb = some (rt, [w]) ∧ w.val = .loc ad 0 ∧ evalAt th.env ib = some (rti, [wi]) ∧
      numOf [wi] = some n ∧ ad.label = m.loc.label ∧ (CE η).sto m.loc.label = some c ∧
      ∀ N el us, c.ty = .array (.lit N) el → accs el = some us → m.loc.offset < (n + 1) * nWords us := by
  refine ⟨x, bb, ib, v, e, hterm, ?_⟩
  rcases hsw with ⟨x', op, e', hterm', hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hterm', -⟩
  · rw [hterm] at hterm'
    simp only [Expr.let_.injEq] at hterm'
    obtain ⟨rfl, rfl, rfl⟩ := hterm'
    rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop', -⟩
    · have hT' := hT
      rw [hterm] at hT'
      cases hT' with
      | let_ hop _ => rw [hl]; exact TermAnch.Flat.bufInit_siteB (η := η) hop hi hE htv hu (TermFul.OneAt_lt hj)
    · cases hop'
  · rw [hterm] at hterm'; cases hterm'
end
end TermWrSiteA.Flat

-- PORTB TermWrSiteA.lean:169 wrSiteA_ok
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wrSiteA_okBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hvr : TermSeenHid.EnvVR th) (hr : r ∈ tstep g mem pairs th) :
    WrSiteA g (CE η) mem pairs th r := by
  intro t m ht hmt
  by_cases hlt : t < mem.size
  · have hm0 : mem[t]? = some mem[t] := by simp [hlt]
    have e2 := (TermFul.tstep_grow hr).1 t _ hm0
    rw [hmt] at e2
    simp only [Option.some.injEq] at e2
    have hm1 : mem[t]? = some m := by rw [hm0, e2]
    by_cases htp : t ∈ th.promises
    · obtain ⟨m', hm', hsw, -, -⟩ :=
        (TermFul.tstep_fulfil (MemInv_promLtB hm) (MemInv_nopairB hm) hr).2 t htp ht
      have hm'' : mem[t]? = some m' := hm'
      rw [hm1] at hm''; cases hm''
      have hss := TermTyped.scopeD_SW hsc hsw
      rcases TermPlantF.Flat.SWIniBN hE hT htv hi hm hss hsw with ⟨c, hc, hI⟩ | ⟨x, bb, ib, v, e, hterm⟩
      · rcases ful_xBN hE hT htv hi hm hss hvr hr htp ht hsw with ⟨c', hc', hx⟩ | ⟨x, bb, ib, v, e, hterm⟩
        · rw [hc] at hc'; cases hc'
          refine .inr (.inr (.inl ⟨c, hc, hI, ?_⟩))
          rcases hx with h | h | h
          · exact .inl h
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr h))
        · exact .inr (.inr (.inr (buf_xBN hE hT htv hi hsw hterm)))
      · exact .inr (.inr (.inr (buf_xBN hE hT htv hi hsw hterm)))
    · exact .inl ⟨htp, hm1⟩
  · have hge : mem.size ≤ t := Nat.le_of_not_lt hlt
    rcases TermAnch.Flat.wrSite_okBN hE hT htv hi hm hsc hr t m ht hmt with h | h | ⟨c, hc, hI⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨c, hc, hI, .inr (.inl hge)⟩))
    · exact .inr (.inr (.inr h))
end
end TermWrSiteA.Flat

-- PORTB TermWrSiteA.lean:206 wrSiteA_okU
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wrSiteA_okUBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term)
    (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws →
      w.view ≤ w.rts) (hr : r ∈ tstep g mem pairs th) :
    WrSiteA g (CE η) mem pairs th r :=
  wrSiteA_okBN hE hT htv hi hm hsc hvr hr
end
end TermWrSiteA.Flat


