/-
**The symbolic relation up to a buffer's literal lengths** (ISA-neutral):
the lowering binds a new buffer at `newBufTy τ`, a zero-length, zero-ini
array, where the source binds it at its allocated length and initialised
count (`src_newBuf_step`). `SRep` asks the types to be equal; `SRepE` asks
them equal up to those two literals (`Ty.eraseLen`), so a node may follow a
buffer the walk allocated. Every symbolic step the relation follows
(`sstep`) is invariant under the erasure.

- `Ty.eraseLen`: a refined locative of a literal-length array at a literal
  ini count, at length and count `0`, through pairs; `accs_eraseLen`,
  `bufElem_eraseLen`, `cellOf_eraseLen`, and the inversions
  `eraseLen_eq_prod`, `eraseLen_eq_iex`;
- `SRepE`, `SRep.toE`, `SRepE.lookup/bind/sub/evalAt/congr`;
- `sstepE_sound`, `srunE_sound`: the symbolic steps sound for `SRepE`;
- `NodeJE`, `NodeJ.toE`, `NodeJE.run`, `NodeJE.step`: the node invariant
  at `SRepE` (`NodeJ`'s twins);
- `SEnv.retype`, `lookupS_retype(_pls/_isSome/_word)`, `SRepE.toSRep`: back
  to `SRep` at the source's types, the placements kept.
-/
import Spike.Lib.Form

namespace Spike.Lib.Form

open CoreLang CoreTerm
open Scc.Sem (ValRep)
open Scc.IR (Operand)

/-! ## The erasure -/

/-- **A buffer type at length and ini count `0`**: a refined locative of a
literal-length array at a literal ini count (`newBuf`'s type at its
allocation), through pairs; every other type kept. -/
def _root_.CoreLang.Ty.eraseLen : Ty → Ty
  | .prod a b => .prod a.eraseLen b.eraseLen
  | .refine (.loc μ (.array (.lit _) u)) (.ini (.lit _)) => .refine (.loc μ (.array (.lit 0) u)) (.ini (.lit 0))
  | t => t

/-- **The erasure keeps the accesses.** -/
theorem accs_eraseLen (t : Ty) : TermRun.accs t.eraseLen = TermRun.accs t := by
  unfold Ty.eraseLen
  split
  · rename_i a b
    simp only [TermRun.accs, accs_eraseLen a, accs_eraseLen b]
  · rfl
  · rfl

/-- **The erasure keeps a buffer's element.** -/
theorem bufElem_eraseLen (t : Ty) : TermRun.bufElem t.eraseLen = TermRun.bufElem t := by
  unfold Ty.eraseLen
  split <;> rfl

/-- **The erasure keeps a reference's cell.** -/
theorem cellOf_eraseLen (t : Ty) : CoreTerm.cellOf t.eraseLen = CoreTerm.cellOf t := by
  unfold Ty.eraseLen
  split <;> rfl

/-- **The erasure keeps the placements' grouping.** -/
theorem grp_eraseLen (t : Ty) (os : List Operand) : grp t.eraseLen os = grp t os := by
  unfold Ty.eraseLen
  split
  · rename_i a b
    simp only [grp, grp_eraseLen a, grp_eraseLen b]
  · rcases os with _ | ⟨o, _ | ⟨o', os⟩⟩ <;> rfl
  · rfl

theorem group_eraseLen (t : Ty) (os : List Operand) : group t.eraseLen os = group t os := by
  simp only [group, grp_eraseLen]

/-- **Types equal up to the erasure group alike.** -/
theorem group_of_eraseLen {t t' : Ty} (h : t'.eraseLen = t.eraseLen) (os : List Operand) :
    group t' os = group t os := by
  rw [← group_eraseLen t', h, group_eraseLen]

/-- **A pair's erasure is only a pair's.** -/
theorem eraseLen_eq_prod {t a b : Ty} (h : t.eraseLen = .prod a b) :
    ∃ u v, t = .prod u v ∧ u.eraseLen = a ∧ v.eraseLen = b := by
  unfold Ty.eraseLen at h
  split at h
  · rename_i u v
    simp only [Ty.prod.injEq] at h
    exact ⟨u, v, rfl, h.1, h.2⟩
  · cases h
  · subst h
    rename_i hne _
    exact absurd rfl (hne _ _)

/-- **An index package's erasure is itself.** -/
theorem eraseLen_eq_iex {t b : Ty} (h : t.eraseLen = .iex b) : t = .iex b := by
  unfold Ty.eraseLen at h
  split at h
  · cases h
  · cases h
  · exact h

/-! ## The relation -/

variable {lbl : WeakMem.AllocLabel → Option Nat} {val : Operand → Option Nat}

/-- **The symbolic environment represents the source's up to the buffers'
literal lengths**: `SRep` with each variable's source type equal to the
symbolic one after `Ty.eraseLen`. -/
def SRepE (lbl : WeakMem.AllocLabel → Option Nat) (val : Operand → Option Nat) (s : SEnv) (env : TermRun.Env) :
    Prop :=
  ∀ x t pls, lookupS s x = some (t, pls) → ∃ t' ws, TermRun.lookupE env x = some (t', ws) ∧
    t'.eraseLen = t.eraseLen ∧ WordsRep lbl val ws pls

/-- **`SRep` is `SRepE`.** -/
theorem SRep.toE {s : SEnv} {env : TermRun.Env} (h : SRep lbl val s env) : SRepE lbl val s env :=
  fun x t pls hx => let ⟨ws, hl, hr⟩ := h x t pls hx; ⟨t, ws, hl, rfl, hr⟩

namespace SRepE

theorem lookup {s : SEnv} {env : TermRun.Env} (h : SRepE lbl val s env) {x : String} {t : Ty}
    {pls : List WordPl} (hx : lookupS s x = some (t, pls)) :
    ∃ t' ws, TermRun.lookupE env x = some (t', ws) ∧ t'.eraseLen = t.eraseLen ∧ WordsRep lbl val ws pls :=
  h x t pls hx

/-- **Binding `x`** on both sides, at types equal up to the erasure. -/
theorem bind {s : SEnv} {env : TermRun.Env} (h : SRepE lbl val s env) (x : String) {t t' : Ty}
    (ht : t'.eraseLen = t.eraseLen) {ws : List TermRun.Word} {pls : List WordPl} (hw : WordsRep lbl val ws pls) :
    SRepE lbl val ((x, t, pls) :: s) ((x, t', ws) :: env) := by
  intro y u q hy
  by_cases hyx : x = y
  · subst hyx
    simp only [lookupS, List.find?_cons, beq_self_eq_true, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨t', ws, by simp [TermRun.lookupE], ht, hw⟩
  · have hne : (x == y) = false := by simp [hyx]
    simp only [lookupS, List.find?_cons, hne] at hy
    obtain ⟨t'', ws', hl, he, hr⟩ := h y u q hy
    exact ⟨t'', ws', by simpa [TermRun.lookupE, List.find?_cons, hne] using hl, he, hr⟩

/-- **Forgetting variables.** -/
theorem sub {s s' : SEnv} {env : TermRun.Env} (h : SRepE lbl val s env)
    (hs : ∀ b ∈ s', lookupS s b.1 = some b.2) : SRepE lbl val s' env := by
  intro x t pls hx
  simp only [lookupS, Option.map_eq_some_iff] at hx
  obtain ⟨b, hb, hbe⟩ := hx
  have hbx : b.1 = x := by simpa using List.find?_some hb
  have := hs b (List.mem_of_find?_eq_some hb)
  rw [hbx, hbe] at this
  exact h x _ _ this

theorem evalAt {s : SEnv} {env : TermRun.Env} (h : SRepE lbl val s env)
    (hval : ∀ n : UInt64, val (.imm n) = some n.toNat) {a : At} {t : Ty} {pls : List WordPl}
    (ha : sevalAt s a = some (t, pls)) :
    ∃ t' ws, TermRun.evalAt env a = some (t', ws) ∧ t'.eraseLen = t.eraseLen ∧ WordsRep lbl val ws pls := by
  cases a with
  | var x => exact h.lookup ha
  | lit n =>
    simp only [sevalAt] at ha
    split at ha
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      refine ⟨_, _, rfl, rfl, ⟨n, ?_, hn, rfl⟩, trivial⟩
      rw [hval]; simp [Nat.mod_eq_of_lt hn]
    · cases ha
  | unit =>
    simp only [sevalAt, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact ⟨_, [], rfl, rfl, trivial⟩

/-- **Changing the operand values** off every placed operand. -/
theorem congr {s : SEnv} {env : TermRun.Env} (h : SRepE lbl val s env) {val' : Operand → Option Nat}
    (hv : ∀ b ∈ s, ∀ pl ∈ b.2.2, ∀ o ∈ pl.opds, val' o = val o) : SRepE lbl val' s env := by
  intro x t pls hx
  obtain ⟨t', ws, hl, he, hr⟩ := h x t pls hx
  simp only [lookupS, Option.map_eq_some_iff] at hx
  obtain ⟨b, hb, hbe⟩ := hx
  exact ⟨t', ws, hl, he, hr.congr fun pl hp => hv b (List.mem_of_find?_eq_some hb) pl (by rw [hbe]; exact hp)⟩

end SRepE

/-- **A symbolic step is the source's local step**, `SRepE` kept
(`sstep_sound` up to the erasure: a pair's halves and accesses, an index
package, kept by it). -/
theorem sstepE_sound {p : Prog} {c : Ctl} {s s' : SEnv} {t' : Expr} (h : SRepE lbl val s c.env)
    (hval : ∀ n : UInt64, val (.imm n) = some n.toNat) (hs : sstep s c.term = some (t', s')) :
    ∃ env', LocalStep p c ⟨t', env', none⟩ ∧ SRepE lbl val s' env' := by
  obtain ⟨term, env⟩ := c
  simp only at h hs ⊢
  unfold sstep at hs
  split at hs
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨t1, ws, hw, hE, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_atom rfl hw, h.bind _ hE hr⟩
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨t1, ws, hw, hE, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_nameI rfl hw, h.bind _ hE hr⟩
  · rename_i x a b e
    cases ha : sevalAt s a with
    | none => simp [ha] at hs
    | some tp =>
    cases hb : sevalAt s b with
    | none => simp [ha, hb] at hs
    | some uq =>
    obtain ⟨t, pa⟩ := tp
    obtain ⟨u, pb⟩ := uq
    simp only [ha, hb] at hs
    cases hs
    obtain ⟨t1, ws, hw, hE, hr⟩ := h.evalAt hval ha
    obtain ⟨u1, us, hu, hE', hr'⟩ := h.evalAt hval hb
    refine ⟨_, localStep_pair rfl hw hu, h.bind _ ?_ (hr.append hr')⟩
    simp only [Ty.eraseLen, hE, hE']
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨t1, ws, hw, -, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_pack rfl hw, h.bind _ rfl hr⟩
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨t1, ws, hw, -, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_packT rfl hw, h.bind _ rfl hr⟩
  · rename_i x sg w n e
    split at hs
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨_, localStep_asLanes (n := n) rfl rfl (by simp [TermRun.numOf, TermRun.cst, Promises.TVal.mk0]),
        h.bind _ rfl ⟨⟨n, ?_, ?_⟩, trivial⟩⟩
      · rw [hval]; simp [Nat.mod_eq_of_lt hn]
      · simp [TermRun.cst, Promises.TVal.mk0, ValRep, TermRun.W64, Nat.mod_eq_of_lt hn, hn]
    · cases hs
  · split at hs
    · rename_i u v pls ha
      obtain ⟨us, hu, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      obtain ⟨t1, ws, hw, hE, hr⟩ := h.evalAt hval ha
      obtain ⟨u1, v1, rfl, hu1, hv1⟩ := eraseLen_eq_prod (hE.trans rfl)
      have hu' : TermRun.accs u1 = some us := by rw [← accs_eraseLen, hu1, accs_eraseLen]; exact hu
      exact ⟨_, localStep_split rfl hw hu', (h.bind _ hu1 (hr.take _)).bind _ hv1 (hr.drop _)⟩
    · cases hs
  · split at hs
    · rename_i b pls ha
      cases hs
      obtain ⟨t1, ws, hw, hE, hr⟩ := h.evalAt hval ha
      obtain rfl := eraseLen_eq_iex hE
      exact ⟨_, localStep_unpack rfl hw, h.bind _ rfl hr⟩
    · cases hs
  · cases hs

/-- **A symbolic run is a local run of the source**, `SRepE` kept. -/
theorem srunE_sound {p : Prog} (hval : ∀ n : UInt64, val (.imm n) = some n.toNat) :
    ∀ (k : Nat) {c : Ctl} {s s' : SEnv} {t' : Expr}, c.hold = none → SRepE lbl val s c.env →
      srun k s c.term = some (t', s') → ∃ env', LocalRun p c ⟨t', env', none⟩ ∧ SRepE lbl val s' env'
  | 0, c, s, s', t', hc, h, hs => by
    simp only [srun, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨t, env, hold⟩ := c
    cases hc
    exact ⟨env, .refl _, h⟩
  | k + 1, c, s, s', t', hc, h, hs => by
    simp only [srun, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨t₁, s₁⟩, h1, h2⟩ := hs
    obtain ⟨env₁, hl, hr⟩ := sstepE_sound (p := p) h hval h1
    obtain ⟨env', hl', hr'⟩ := srunE_sound hval k (c := ⟨t₁, env₁, none⟩) rfl hr h2
    exact ⟨env', .step hl hl', hr'⟩

/-! ## The node invariant up to the erasure -/

/-- **The invariant at a node up to the buffers' literal lengths**: `NodeJ`
at `SRepE`. -/
def NodeJE (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (t : Expr) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  c.term = t ∧ c.hold = none ∧ SRepE lbl (opdVal rs sl) s c.env

/-- **`NodeJ` is `NodeJE`.** -/
theorem NodeJ.toE {rs : Scc.IR.Reg → Option Int} {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl}
    (h : NodeJ lbl rs t s sl c) : NodeJE lbl rs t s sl c :=
  ⟨h.1, h.2.1, h.2.2.toE⟩

/-- **An edge through code-free forms** (`NodeJ.run` at `NodeJE`). -/
theorem NodeJE.run {rs : Scc.IR.Reg → Option Int} {p : Prog}
    {t t' : Expr} {s s₁ s₂ : SEnv} {sl sl' : Int → BitVec 64} {c : Ctl} (h : NodeJE lbl rs t s sl c) (k : Nat)
    (hr : srun k s t = some (t', s₁)) (hsub : ∀ b ∈ s₂, lookupS s₁ b.1 = some b.2)
    (hsl : ∀ b ∈ s₂, ∀ pl ∈ b.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    ∃ c', LocalRun p c c' ∧ NodeJE lbl rs t' s₂ sl' c' := by
  obtain ⟨ht, hc, hs⟩ := h
  rw [← ht] at hr
  obtain ⟨env', hl, hr'⟩ := srunE_sound (p := p) (opdVal_imm rs sl) k hc hs hr
  exact ⟨_, hl, rfl, rfl, (hr'.sub hsub).congr hsl⟩

/-- **A node's invariant after one local step that binds `x`** (`NodeJ.step`
at `NodeJE`, the symbolic type `ty` and the source's `ty'` equal up to the
erasure). -/
theorem NodeJE.step {rs : Scc.IR.Reg → Option Int} {p : Prog}
    {t e : Expr} {s : SEnv} {sl sl' : Int → BitVec 64} {c : Ctl} {x : String} {ty ty' : Ty}
    {ws : List TermRun.Word} {pls : List WordPl} (h : NodeJE lbl rs t s sl c)
    (hst : LocalStep p c ⟨e, (x, ty', ws) :: c.env, none⟩) (hE : ty'.eraseLen = ty.eraseLen)
    (hw : WordsRep lbl (opdVal rs sl') ws pls)
    (hsl : ∀ b ∈ s, ∀ pl ∈ b.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    LocalRun p c ⟨e, (x, ty', ws) :: c.env, none⟩ ∧
      NodeJE lbl rs e ((x, ty, pls) :: s) sl' ⟨e, (x, ty', ws) :: c.env, none⟩ :=
  ⟨.single hst, rfl, rfl, (h.2.2.congr hsl).bind x hE hw⟩

/-! ## Back to `SRep`, at the source's types -/

/-- **The symbolic environment at the source's types**: each binding's type
the source's for that variable (where bound), its placements kept. -/
def SEnv.retype (env : TermRun.Env) (s : SEnv) : SEnv :=
  s.map fun b => (b.1, ((TermRun.lookupE env b.1).map (·.1)).getD b.2.1, b.2.2)

theorem lookupS_retype (env : TermRun.Env) (s : SEnv) (x : String) :
    lookupS (s.retype env) x =
      (lookupS s x).map fun b => (((TermRun.lookupE env x).map (·.1)).getD b.1, b.2) := by
  unfold lookupS SEnv.retype
  rw [List.find?_map]
  cases h : s.find? (·.1 == x) with
  | none =>
    have : List.find? ((fun b : String × Ty × List WordPl => b.1 == x) ∘
        fun b => (b.1, ((TermRun.lookupE env b.1).map (·.1)).getD b.2.1, b.2.2)) s = none := h
    simp [this]
  | some b =>
    have : List.find? ((fun b : String × Ty × List WordPl => b.1 == x) ∘
        fun b => (b.1, ((TermRun.lookupE env b.1).map (·.1)).getD b.2.1, b.2.2)) s = some b := h
    have hx : b.1 = x := by simpa using List.find?_some h
    simp [this, hx]

/-- **Retyping keeps the placements.** -/
theorem lookupS_retype_pls (env : TermRun.Env) (s : SEnv) (x : String) :
    (lookupS (s.retype env) x).map (·.2) = (lookupS s x).map (·.2) := by
  rw [lookupS_retype]; cases lookupS s x <;> rfl

/-- **Retyping keeps what is bound.** -/
theorem lookupS_retype_isSome (env : TermRun.Env) (s : SEnv) (x : String) :
    (lookupS (s.retype env) x).isSome = (lookupS s x).isSome := by
  rw [lookupS_retype]; cases lookupS s x <;> rfl

/-- **Retyping keeps each word's placement.** -/
theorem lookupS_retype_word (env : TermRun.Env) (s : SEnv) (x : String) (k : Nat) :
    (lookupS (s.retype env) x).bind (·.2[k]?) = (lookupS s x).bind (·.2[k]?) := by
  rw [lookupS_retype]; cases lookupS s x <;> rfl

/-- **`SRepE` is `SRep` at the source's types.** -/
theorem SRepE.toSRep {s : SEnv} {env : TermRun.Env} (h : SRepE lbl val s env) :
    SRep lbl val (s.retype env) env := by
  intro x t pls hx
  rw [lookupS_retype] at hx
  obtain ⟨⟨t0, q⟩, h0, he⟩ := Option.map_eq_some_iff.mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨t', ws, hl, -, hr⟩ := h x t0 _ h0
  exact ⟨ws, by rw [hl]; rfl, hr⟩

/-! ## Tests -/

/-- `newBuf`'s source type and the lowering's agree up to the erasure. -/
example (k ini : Nat) (u : Ty) :
    (Ty.refine (.loc .own (.array (.lit k) u)) (.ini (.lit ini))).eraseLen =
      (Ty.refine (.loc .own (.array (.lit 0) u)) (.ini (.lit 0))).eraseLen := rfl

/-- A pair of buffers too. -/
example (k : Nat) (u : Ty) :
    (Ty.prod (.refine (.loc .own (.array (.lit k) u)) (.ini (.lit k))) .int).eraseLen =
      (Ty.prod (.refine (.loc .own (.array (.lit 0) u)) (.ini (.lit 0))) .int).eraseLen := rfl

/-- info: 'Spike.Lib.Form.sstepE_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sstepE_sound

/-- info: 'Spike.Lib.Form.srunE_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms srunE_sound

/-- info: 'Spike.Lib.Form.NodeJE.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NodeJE.run

/-- info: 'Spike.Lib.Form.NodeJE.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NodeJE.step

/-- info: 'Spike.Lib.Form.SRepE.toSRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SRepE.toSRep

end Spike.Lib.Form
