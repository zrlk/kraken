/-
**The simulation behind Lemma 1's
projection direction** (`PromProjection`, `LiveBridge.lean`). ISA-neutral and
architecture-neutral; executable `Thread` rules only (`stepOne`/`runTree`), no
machine (`succs`, `StepSem`) is involved here.

Setting. `M` is the memory before the promise (`m = |M|`), `w` a message of
thread `tid`. The **post-run** (`c`, `t`: the "real" side) is a solo run of the
thread that has promised `w` at `m + 1`, against `M ++ [w] ++ …`; the
**pre-run** (`c'`, `t'`: the replay) is a solo run of the thread without that
promise, against `M ++ …`. The pre-run mirrors the post-run step by step:

- *phase A* (`out = true`: `w` still outstanding in the post-run): the
  thread's fresh writes sit one timestamp lower in the pre-run;
- *the fulfilment* of `m + 1` in the post-run is a fresh write ("promise
  now") of `w` in the pre-run, with the same constraining view, which is
  `≤ m` because the fulfilment needs it `< m + 1`;
- *phase B* (`out = false`): the two memories hold the same messages above
  `m`, in a different order (`w` first in the post-run, after the phase-A
  writes in the pre-run).

The relation does not track timestamps above `m` exactly. Views agree once
clamped at `m + 1` (`VR`, from `ReleasePrefixNT.lean`); every message above
`m` is the thread's own; and per location the *last* performed own write
above `m` is the same message on both sides (`LatRel`, `FwdLast`). This is
enough because a thread's coherence view of a location is at least each of
its own performed writes to it (`ownR`), so a read that sees past `m` must
read the last own write to its location, on both sides.

Contents:
- `Pf`, `IsLast`, `FwdLast`, `LatRel`, `outL`: the vocabulary;
- `Ctx.PSim`: the context relation;
- `readSuccs_psim`: one read; `write_now_psim`, `write_ful_psim`,
  `write_trans_psim`, `writeSuccs_psim`: one write (fresh, fulfilment above
  `m + 1`, the fulfilment of `m + 1`);
- `fenceStep_psim`, `fenceOpt_psim`, `rmwPost_psim`, `xclFail_psim`: the
  silent rules; `runTree_psim`: one event tree;
- `Thread.PSim`, `stepOne_psim`: one instruction (used by
  `PromProjection.lean`).
-/
import Kraken.Promising.ReleasePrefixNT

namespace Kraken.Promising.Proj

open Kraken.Promising

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Vocabulary -/

/-- `u` is a *performed* write of the post-run: not the outstanding promise
`m + 1` while it is outstanding (`out`). -/
def Pf (m : Nat) (out : Bool) (u : Time) : Prop := out = true → u ≠ m + 1

theorem Pf.of_false {m : Nat} {u : Time} : Pf m false u := fun h => Bool.noConfusion h

theorem Pf.of_true {m : Nat} {out : Bool} {u : Time} (h : Pf m true u) : Pf m out u :=
  fun _ => h rfl

/-- `s` is the last performed write to `l` above `m` in `mem`. -/
structure IsLast (mem : Memory) (m : Nat) (out : Bool) (l : Loc) (s : Time) : Prop where
  gt : m < s
  pf : Pf m out s
  msg : ∃ x, mem.get? s = some x ∧ x.loc = l
  last : ∀ s' x, s < s' → Pf m out s' → mem.get? s' = some x → x.loc ≠ l

/-- Forwarding entries above `m` are at the last performed write to their
location. -/
def FwdLast (mem : Memory) (m : Nat) (out : Bool) (vs : Views) : Prop :=
  ∀ l f, vs.getFwd l = some f → m < f.time → IsLast mem m out l f.time

/-- Above `m`, per location, the post-memory `memq` and the pre-memory `memp`
agree on the last performed write, and every pre-message above `m` has a
performed post-message to the same location above `m`. -/
structure LatRel (m : Nat) (out : Bool) (memq memp : Memory) : Prop where
  fwd : ∀ l s x, IsLast memq m out l s → memq.get? s = some x →
    ∃ s', IsLast memp m false l s' ∧ memp.get? s' = some x
  back : ∀ u x, m < u → memp.get? u = some x →
    ∃ s y, m < s ∧ Pf m out s ∧ memq.get? s = some y ∧ y.loc = x.loc

/-- The outstanding promise, as a list. -/
def outL (m : Nat) (out : Bool) : List Time := if out then [m + 1] else []

/-! ### Facts about the vocabulary -/

theorem IsLast.unique {mem : Memory} {m : Nat} {out : Bool} {l : Loc} {a b : Time}
    (ha : IsLast mem m out l a) (hb : IsLast mem m out l b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · obtain ⟨x, hx, hl⟩ := hb.msg
    exact absurd hl (ha.last b x h hb.pf hx)
  · exact h
  · obtain ⟨x, hx, hl⟩ := ha.msg
    exact absurd hl (hb.last a x h ha.pf hx)

theorem IsLast.append_ne {mem : Memory} {m : Nat} {out : Bool} {l : Loc} {s : Time} (h : IsLast mem m out l s)
    {x : Msg} (hx : x.loc ≠ l) : IsLast (mem.append x).1 m out l s := by
  obtain ⟨y, hy, hyl⟩ := h.msg
  refine ⟨h.gt, h.pf, ⟨y, by rw [Memory.get?_append_of_le _ _ _ (mem.last_le_of_get?_eq_some hy)]; exact hy, hyl⟩,
    fun s' z hs' hp hz => ?_⟩
  rcases Memory.get?_append_eq_some _ _ hz with ⟨-, hz'⟩ | ⟨-, rfl⟩
  · exact h.last s' z hs' hp hz'
  · exact hx

theorem IsLast.of_append {mem : Memory} {m : Nat} {out : Bool} {l : Loc} {s : Time} {x : Msg}
    (h : IsLast (mem.append x).1 m out l s) (hx : x.loc ≠ l) : IsLast mem m out l s := by
  obtain ⟨y, hy, hyl⟩ := h.msg
  rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
  · refine ⟨h.gt, h.pf, ⟨y, hy', hyl⟩, fun s' z hs' hp hz => h.last s' z hs' hp ?_⟩
    rw [Memory.get?_append_of_le _ _ _ (mem.last_le_of_get?_eq_some hz)]; exact hz
  · exact absurd hyl hx

theorem IsLast.append_new {mem : Memory} {m : Nat} {out : Bool} (x : Msg) (hm : m ≤ mem.last)
    (hp : Pf m out (mem.last + 1)) : IsLast (mem.append x).1 m out x.loc (mem.last + 1) := by
  refine ⟨by omega_t, hp, ⟨x, Memory.get?_append_last _ _, rfl⟩, fun s' z hs' _ hz => ?_⟩
  have := (mem.append x).1.last_le_of_get?_eq_some hz
  rw [Memory.last_append] at this; omega_t

theorem IsLast.eq_new {mem : Memory} {m : Nat} {out : Bool} {x : Msg} {s : Time}
    (h : IsLast (mem.append x).1 m out x.loc s) (hp : Pf m out (mem.last + 1)) : s = mem.last + 1 := by
  have hs : s ≤ mem.last + 1 := by
    obtain ⟨y, hy, -⟩ := h.msg
    have := (mem.append x).1.last_le_of_get?_eq_some hy
    rw [Memory.last_append] at this; exact this
  rcases Nat.lt_or_ge s (mem.last + 1) with hlt | hge
  · exact absurd rfl (h.last _ x hlt hp (Memory.get?_append_last _ _))
  · omega_t

/-- A message at a nonzero timestamp is read at its location. -/
theorem read?_of_get? {mem : Memory} {s : Time} {x : Msg} (h : mem.get? s = some x) (hs : s ≠ 0) :
    mem.read? x.loc s = some x.val := by
  unfold Memory.read?
  simp [hs, h]

/-! ## The context relation -/

/-- **The post-run context `c` and the pre-run context `c'`** of one
instruction (thread `tid`; `M` the memory before the promise of `w`; `out`:
`w` is still outstanding in the post-run; `B`: the instruction started in
phase B). See the module docstring. -/
structure _root_.Kraken.Promising.Ctx.PSim (M : Memory) (tid : Nat) (w : Msg) (out : Bool) (B : Prop) (c c' : Ctx) : Prop where
  rel : c.Rel M.last c'
  promEq : c.prom = c'.prom ++ outL M.last out
  promLe : ∀ s ∈ c'.prom, s ≤ M.last
  memR : M.Prefix c.mem
  memP : M.Prefix c'.mem
  outW : out = true → c.mem.get? (M.last + 1) = some w
  tidR : ∀ u x, M.last < u → c.mem.get? u = some x → x.tid = tid
  tidP : ∀ u x, M.last < u → c'.mem.get? u = some x → x.tid = tid
  ownR : ∀ u x, M.last < u → Pf M.last out u → c.mem.get? u = some x → u ≤ c.views.getCoh x.loc
  fwdR : FwdLast c.mem M.last out c.views
  fwdP : FwdLast c'.mem M.last false c'.views
  lat : LatRel M.last out c.mem c'.mem
  bnd : c'.Bnd
  /-- Once `w` is fulfilled, the pre-run has written it as "promise now"
  with a constraining view `≤ |M|` during this instruction (unless the
  instruction started in phase B). -/
  pnow : out = false → B ∨ ∃ ν, ν ≤ M.last ∧ (w, ν) ∈ c'.promisedNow

section Facts

variable {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {B : Prop} {c c' : Ctx}

/-- Every post-promise is in the post-memory. -/
theorem _root_.Kraken.Promising.Ctx.PSim.prom_le_last (hs : c.PSim M tid w out B c') : ∀ s ∈ c.prom, s ≤ c.mem.last := by
  intro s h
  rw [hs.promEq, List.mem_append] at h
  rcases h with h | h
  · exact Nat.le_trans (hs.promLe s h) hs.memR.last_le
  · unfold outL at h
    split at h
    · rename_i ho
      rw [List.mem_singleton] at h; subst h
      exact c.mem.last_le_of_get?_eq_some (hs.outW ho)
    · cases h

/-- The fresh timestamp of the post-memory is performed. -/
theorem _root_.Kraken.Promising.Ctx.PSim.pf_fresh (hs : c.PSim M tid w out B c') : Pf M.last out (c.mem.last + 1) := by
  intro ho
  have := c.mem.last_le_of_get?_eq_some (hs.outW ho)
  omega_t

/-- The replay's exclusive check passes: at or below `m` it sees what the
post-run saw (`hr`), above `m` only the thread's own messages. -/
theorem _root_.Kraken.Promising.Ctx.PSim.atomic (hs : c.PSim M tid w out B c') {l : Loc} {r a tq tp : Time} (hra : VR M.last r a)
    (hr : r ≤ M.last → c.mem.atomic l tid r tq = true) (hq : M.last < tq) :
    c'.mem.atomic l tid a tp = true := by
  by_cases ham : a ≤ M.last
  · have e : r = a := hra.eq' ham
    subst e
    cases hrd : c'.mem.read? l r with
    | none => unfold Memory.atomic; rw [hrd]
    | some val =>
      have hrd0 : c.mem.read? l r = some val := by rw [hs.memR.read? ham, ← hs.memP.read? ham]; exact hrd
      apply Memory.atomic_of_forall
      intro u x h1 h2 hx hl
      by_cases hum : u ≤ M.last
      · rw [hs.memP.get? hum, ← hs.memR.get? hum] at hx
        exact Memory.atomic_elim (hr ham) hrd0 u x h1 (by omega_t) hx hl
      · exact hs.tidP u x (by omega_t) hx
  · apply Memory.atomic_of_forall
    intro u x h1 _ hx _
    exact hs.tidP u x (by omega_t) hx

end Facts

/-! ## One read -/

section Rules

variable (A : Arch) (tid : Nat)

/-- **One read, replayed.** A read of the post-run is matched by a read of
the pre-run of the same value: of the same timestamp at or below `m`, else
of the last own write to the location (the same message). -/
theorem readSuccs_psim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.PSim M tid w out B c') (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last)
    {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    ∃ x' ∈ readSuccs A iv' c' k xcl l noRet, x'.2.1 = x.2.1 ∧ VR M.last x.1 x'.1 ∧ x'.1 ≤ c'.mem.last ∧
      x.2.2.PSim M tid w out B x'.2.2 := by
  obtain ⟨t, v, rfl, htl, hv, hw, hp⟩ := (mem_readSuccs A).mp hx
  have hrel := hs.rel.views
  have hpre : VR M.last (readPre A iv c k) (readPre A iv' c' k) :=
    hiv.addrR.max (hrel.vrNew.max (VR.ite hrel.vRel (VR.refl _ _)))
  have hB : VR M.last (max (readPre A iv c k) (c.views.getCoh l)) (max (readPre A iv' c' k) (c'.views.getCoh l)) :=
    hpre.max (hrel.coh l)
  have hML := hs.memP.last_le
  -- a write to `l` above `t` in the post-memory, within the bound, contradicts the read
  have hnw : ∀ u y, t < u → u ≤ max (readPre A iv c k) (c.views.getCoh l) → c.mem.get? u = some y →
      y.loc = l → False := by
    intro u y h1 h2 hy hl
    rw [(Memory.writeIn_iff _ _ _ _).mpr ⟨u, y, h1, h2, hy, hl⟩] at hw; cases hw
  have hcoh : c.views.getCoh l ≤ max (readPre A iv c k) (c.views.getCoh l) := Nat.le_max_right _ _
  obtain ⟨t', ht'l, hv', hw', hp', ht', hiff⟩ : ∃ t', t' ≤ c'.mem.last ∧ c'.mem.read? l t' = some v ∧
      c'.mem.writeIn l t' (max (readPre A iv' c' k) (c'.views.getCoh l)) = false ∧
      c'.prom.contains t' = false ∧ VR M.last t t' ∧
      ∀ f g, c.views.getFwd l = some f → c'.views.getFwd l = some g → (f.time = t ↔ g.time = t') := by
    by_cases htm : t ≤ M.last
    · refine ⟨t, by omega_t, by rw [hs.memP.read? htm, ← hs.memR.read? htm]; exact hv, ?_, ?_, VR.refl _ _, ?_⟩
      · rw [Bool.eq_false_iff, Ne, Memory.writeIn_iff]
        rintro ⟨u, y, h1, h2, hy, hl⟩
        by_cases hum : u ≤ M.last
        · rw [hs.memP.get? hum, ← hs.memR.get? hum] at hy
          refine hnw u y h1 ?_ hy hl
          by_cases hbm : max (readPre A iv c k) (c.views.getCoh l) ≤ M.last
          · rw [← hB.eq hbm]; exact h2
          · omega_t
        · obtain ⟨s, z, hs1, hs2, hz, hzl⟩ := hs.lat.back u y (by omega_t) hy
          exact hnw s z (by omega_t) (Nat.le_trans (hs.ownR s z hs1 hs2 hz) (hzl ▸ hl ▸ hcoh)) hz (hzl.trans hl)
      · rw [Bool.eq_false_iff, Ne, List.contains_iff_mem]
        intro h
        have : t ∈ c.prom := by rw [hs.promEq]; exact List.mem_append_left _ h
        rw [List.contains_iff_mem.mpr this] at hp; cases hp
      · intro f g hf hg
        have hfg := hrel.fwd l
        rw [hf, hg] at hfg
        obtain ⟨h1, -, -⟩ := hfg
        constructor
        · intro e; rw [← e] at htm ⊢; exact h1.eq htm
        · intro e; rw [← e] at htm ⊢; exact h1.eq' htm
    · -- above `m`: the last own write to `l`
      have htp : Pf M.last out t := by
        intro ho e
        have : t ∈ c.prom := by
          rw [hs.promEq]; unfold outL; rw [ho]; exact List.mem_append_right _ (List.mem_singleton.mpr e)
        rw [List.contains_iff_mem.mpr this] at hp; cases hp
      rcases Memory.read?_eq_some _ hv with ⟨rfl, -⟩ | ⟨y, hy, hyl, rfl⟩
      · omega_t
      have hlast : IsLast c.mem M.last out l t :=
        ⟨by omega_t, htp, ⟨y, hy, hyl⟩, fun s' z h1 h2 hz hzl =>
          hnw s' z h1 (Nat.le_trans (hs.ownR s' z (by omega_t) h2 hz) (hzl ▸ hcoh)) hz hzl⟩
      obtain ⟨t', hlast', hy'⟩ := hs.lat.fwd l t y hlast hy
      refine ⟨t', c'.mem.last_le_of_get?_eq_some hy', ?_, ?_, ?_, VR.of_gt (by omega_t) hlast'.gt, ?_⟩
      · rw [← hyl]; exact read?_of_get? hy' (by have := hlast'.gt; omega_t)
      · rw [Bool.eq_false_iff, Ne, Memory.writeIn_iff]
        rintro ⟨u, z, h1, -, hz, hzl⟩
        exact hlast'.last u z h1 Pf.of_false hz hzl
      · rw [Bool.eq_false_iff, Ne, List.contains_iff_mem]
        intro h
        have := hs.promLe t' h
        have := hlast'.gt
        omega_t
      · intro f g hf hg
        have hfg := hrel.fwd l
        rw [hf, hg] at hfg
        obtain ⟨h1, -, -⟩ := hfg
        constructor
        · intro e
          have hgm : M.last < g.time := h1.gt (by rw [e]; omega_t)
          exact (hs.fwdP l g hg hgm).unique hlast'
        · intro e
          have hfm : M.last < f.time := h1.gt' (by rw [e]; exact hlast'.gt)
          exact (hs.fwdR l f hf hfm).unique hlast
  have hν : VR M.last (max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t))
      (max (readPre A iv' c' k) (readView A (A.loadKind k) (c'.views.getFwd l) t')) :=
    hpre.max (readView_vr A (hrel.fwd l) ht' hiff)
  have hx' := (mem_readSuccs A (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (noRet := noRet)
    (x := (t', v, readNext A iv' c' k xcl l noRet t' v))).mpr ⟨t', v, rfl, ht'l, hv', hw', hp'⟩
  refine ⟨_, hx', rfl, ht', ht'l, ?_⟩
  have hb' := (readSuccs_bnd A iv' hs.bnd hiv' hx').1
  have hcohle : ∀ l', c.views.getCoh l' ≤ (readNext A iv c k xcl l noRet t v).views.getCoh l' :=
    fun l' => Views.getCoh_le_setCoh _ _ _ _
  exact
    { rel := ⟨Views.Rel.read hrel hν hiv.addrW ht', hs.rel.prom, clampL_append hs.rel.loadViews hν,
        hs.rel.succView, hs.rel.rmwWrote, hs.rel.stores⟩
      promEq := hs.promEq
      promLe := hs.promLe
      memR := hs.memR
      memP := hs.memP
      outW := hs.outW
      tidR := hs.tidR
      tidP := hs.tidP
      ownR := fun u y h1 h2 hy => Nat.le_trans (hs.ownR u y h1 h2 hy) (hcohle _)
      fwdR := hs.fwdR
      fwdP := hs.fwdP
      lat := hs.lat
      bnd := hb'
      pnow := hs.pnow }

/-! ## One fresh write -/

/-- **A fresh write ("promise now"), replayed** (either phase): the post-run
appends at `|Mq| + 1`, the pre-run appends the same message at `|Mp| + 1`. -/
theorem write_now_psim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.PSim M tid w out B c') (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htr' : ∀ a, tr' = some a → a ≤ c'.mem.last)
    {extra extra' : View} (hex : VR M.last extra extra') (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr')
    (hok : WriteOk A tid iv c k l tr extra (c.mem.last + 1)) :
    ∃ c2' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr',
      (afterWrite A iv
        { c with mem := (c.mem.append { loc := l, val := v, tid }).1,
                 prom := c.prom ++ [c.mem.last + 1],
                 promisedNow := c.promisedNow ++
                   [({ loc := l, val := v, tid }, max (writePre A iv c k extra) (c.views.getCoh l))] }
        (A.storeKind k) xcl l v (c.mem.last + 1) (max iv.addrR (max iv.dataR extra)) false xr).PSim
        M tid w out B c2' := by
  have hrel := hs.rel.views
  have hB' := writePre_le A (l := l) hs.bnd hiv' k hex'
  have hML := hs.memP.last_le
  have hMR := hs.memR.last_le
  have hok' : WriteOk A tid iv' c' k l tr' extra' (c'.mem.last + 1) := by
    refine ⟨by omega_t, fun a ha => ⟨by have := htr' a ha; omega_t, ?_⟩⟩
    cases tr with
    | none => cases tr' <;> simp only [OptR] at htr; cases ha
    | some r =>
      cases tr' with
      | none => exact htr.elim
      | some a' =>
        cases ha
        exact hs.atomic htr (fun _ => (hok.2 r rfl).2) (by omega_t)
  have hmem := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
    (extra := extra') (xr := xr')).mpr (Or.inr ⟨hok', rfl⟩)
  refine ⟨_, hmem, ?_⟩
  have ht' : VR M.last (c.mem.last + 1) (c'.mem.last + 1) := VR.of_gt (by omega_t) (by omega_t)
  have hnot' : c'.mem.last + 1 ∉ c'.prom := fun h => by have := hs.promLe _ h; omega_t
  have hnot : c.mem.last + 1 ∉ c.prom := fun h => by have := hs.prom_le_last _ h; omega_t
  have hpe : (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) = c.prom := by
    rw [List.erase_append_right _ hnot]; simp
  have hpe' : (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) = c'.prom := by
    rw [List.erase_append_right _ hnot']; simp
  have hpf := hs.pf_fresh
  exact
    { rel := by
        refine afterWrite_rel A ?_ hiv.addrW _ _ _ _ ht' (hiv.addrR.max (hiv.dataR.max hex)) _ _ hxr ?_
          hs.rel.loadViews hs.rel.rmwWrote hs.rel.stores
        · exact hrel
        · show (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) =
            ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).filter (· ≤ M.last)
          rw [hpe, hpe']; exact hs.rel.prom
      promEq := by
        show (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) =
          (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) ++ outL M.last out
        rw [hpe, hpe']; exact hs.promEq
      promLe := by show ∀ s ∈ (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1), _; rw [hpe']; exact hs.promLe
      memR := hs.memR.trans (Memory.Prefix.append _ _)
      memP := hs.memP.trans (Memory.Prefix.append _ _)
      outW := fun ho => by
        show (c.mem.append _).1.get? _ = _
        rw [Memory.get?_append_of_le _ _ _ (c.mem.last_le_of_get?_eq_some (hs.outW ho))]; exact hs.outW ho
      tidR := fun u y hu hy => by
        rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
        · exact hs.tidR u y hu hy'
        · rfl
      tidP := fun u y hu hy => by
        rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
        · exact hs.tidP u y hu hy'
        · rfl
      ownR := fun u y hu hpf' hy => by
        rw [afterWrite_getCoh]
        rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨rfl, rfl⟩
        · have := hs.ownR u y hu hpf' hy'
          split
          · rename_i e; rw [e] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
          · exact this
        · simp only [↓reduceIte]; exact Nat.le_max_right _ _
      fwdR := fun l' f hf hm => by
        rw [afterWrite_getFwd] at hf
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf
          subst hf
          exact IsLast.append_new _ hMR hpf
        · simp only [e, ↓reduceIte] at hf
          exact (hs.fwdR l' f hf hm).append_ne (fun h => e h.symm)
      fwdP := fun l' f hf hm => by
        rw [afterWrite_getFwd] at hf
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf
          subst hf
          exact IsLast.append_new _ hML Pf.of_false
        · simp only [e, ↓reduceIte] at hf
          exact (hs.fwdP l' f hf hm).append_ne (fun h => e h.symm)
      lat :=
        { fwd := fun l' s y hl hy => by
            by_cases e : l = l'
            · subst e
              have hs1 := hl.eq_new (x := { loc := l, val := v, tid }) hpf
              subst hs1
              have hy1 : (c.mem.append { loc := l, val := v, tid }).1.get? (c.mem.last + 1) = some y := hy
              rw [Memory.get?_append_last] at hy1
              cases hy1
              exact ⟨_, IsLast.append_new _ hML Pf.of_false, Memory.get?_append_last _ _⟩
            · have hl0 := hl.of_append (x := { loc := l, val := v, tid }) e
              obtain ⟨z, hz, -⟩ := hl0.msg
              have hy0 : c.mem.get? s = some y := by
                have hy1 : (c.mem.append { loc := l, val := v, tid }).1.get? s = some y := hy
                rwa [Memory.get?_append_of_le _ _ _ (c.mem.last_le_of_get?_eq_some hz)] at hy1
              obtain ⟨s', h1, h2⟩ := hs.lat.fwd l' s y hl0 hy0
              exact ⟨s', h1.append_ne e, by
                show (c'.mem.append _).1.get? s' = _
                rw [Memory.get?_append_of_le _ _ _ (c'.mem.last_le_of_get?_eq_some h2)]; exact h2⟩
          back := fun u y hu hy => by
            rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
            · obtain ⟨s, z, h1, h2, h3, h4⟩ := hs.lat.back u y hu hy'
              exact ⟨s, z, h1, h2, by
                show (c.mem.append _).1.get? s = _
                rw [Memory.get?_append_of_le _ _ _ (c.mem.last_le_of_get?_eq_some h3)]; exact h3, h4⟩
            · exact ⟨c.mem.last + 1, _, by omega_t, hpf, Memory.get?_append_last _ _, rfl⟩ }
      bnd := (writeSuccs_bnd A tid iv' hs.bnd hiv' hex' hmem).1
      pnow := fun ho => (hs.pnow ho).imp id (fun ⟨ν, h1, h2⟩ => ⟨ν, h1, List.mem_append_left _ h2⟩) }

/-! ## One fulfilment at or below `m` -/

/-- **A fulfilment of a promise at or below `m`, replayed** (either phase):
the same fulfilment in the pre-run. -/
theorem write_ful_psim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.PSim M tid w out B c') (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr')
    {extra extra' : View} (hex : VR M.last extra extra') (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr')
    {t : Time} (htp : t ∈ c.prom) {y : Msg} (hy : c.mem.get? t = some y) (hyl : y.loc = l) (hyv : y.val = v)
    (hyt : y.tid = tid) (hok : WriteOk A tid iv c k l tr extra t) (htm : t ≤ M.last) :
    ∃ c2' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr',
      (afterWrite A iv c (A.storeKind k) xcl l v t (max iv.addrR (max iv.dataR extra)) true xr).PSim
        M tid w out B c2' := by
  have hrel := hs.rel.views
  have hB := (writePre_vr A hrel hiv k hex).max (hrel.coh l)
  have hbt : max (writePre A iv c k extra) (c.views.getCoh l) ≤ M.last := by have := hok.1; omega_t
  have hok' : WriteOk A tid iv' c' k l tr' extra' t := by
    refine ⟨by rw [hB.eq hbt]; exact hok.1, fun a ha => ?_⟩
    cases tr with
    | none => cases tr' <;> simp only [OptR] at htr; cases ha
    | some r =>
      cases tr' with
      | none => exact htr.elim
      | some a' =>
        have e : a' = a := Option.some.inj ha
        subst e
        have hr := hok.2 r rfl
        have hra : a' = r := (show VR M.last r a' from htr).eq (by omega_t)
        subst hra
        refine ⟨hr.1, ?_⟩
        rw [hs.memP.atomic_eq hr.1 htm, ← hs.memR.atomic_eq hr.1 htm]; exact hr.2
  have htp' : t ∈ c'.prom := by
    rw [hs.promEq, List.mem_append] at htp
    rcases htp with h | h
    · exact h
    · unfold outL at h; split at h
      · rw [List.mem_singleton] at h; omega_t
      · cases h
  have hy' : c'.mem.get? t = some y := by rw [hs.memP.get? htm, ← hs.memR.get? htm]; exact hy
  have hmem := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
    (extra := extra') (xr := xr')).mpr (Or.inl ⟨t, htp', y, hy', hyl, hyv, hyt, hok', rfl⟩)
  refine ⟨_, hmem, ?_⟩
  exact
    { rel := afterWrite_rel A hrel hiv.addrW _ _ _ _ (VR.refl _ _) (hiv.addrR.max (hiv.dataR.max hex))
        true true hxr (by rw [hs.rel.prom, List.erase_filter]) hs.rel.loadViews hs.rel.rmwWrote hs.rel.stores
      promEq := by
        show c.prom.erase t = c'.prom.erase t ++ outL M.last out
        rw [hs.promEq, List.erase_append_left _ htp']
      promLe := fun s h => hs.promLe s (List.mem_of_mem_erase h)
      memR := hs.memR
      memP := hs.memP
      outW := hs.outW
      tidR := hs.tidR
      tidP := hs.tidP
      ownR := fun u z h1 h2 hz => Nat.le_trans (hs.ownR u z h1 h2 hz) (Views.getCoh_le_setCoh _ _ _ _)
      fwdR := fun l' f hf hm => by
        rw [afterWrite_getFwd] at hf
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf
          subst hf; simp only at hm; omega_t
        · simp only [e, ↓reduceIte] at hf
          exact hs.fwdR l' f hf hm
      fwdP := fun l' f hf hm => by
        rw [afterWrite_getFwd] at hf
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf
          subst hf; simp only at hm; omega_t
        · simp only [e, ↓reduceIte] at hf
          exact hs.fwdP l' f hf hm
      lat := hs.lat
      bnd := (writeSuccs_bnd A tid iv' hs.bnd hiv' hex' hmem).1
      pnow := hs.pnow }

/-! ## The fulfilment of `w` -/

/-- With `w` outstanding, a performed post-write to `w`'s location above `m`
puts `coh` of it above `m`. -/
theorem IsLast.unout {mem : Memory} {m : Nat} {l : Loc} {s : Time} {w : Msg} (h : IsLast mem m true l s)
    (hw : mem.get? (m + 1) = some w) (hl : w.loc ≠ l) : IsLast mem m false l s := by
  refine ⟨h.gt, Pf.of_false, h.msg, fun s' y h1 _ hy => ?_⟩
  by_cases e : s' = m + 1
  · subst e; rw [hw] at hy; cases hy; exact hl
  · exact h.last s' y h1 (fun _ => e) hy

theorem IsLast.toOut {mem : Memory} {m : Nat} {l : Loc} {s : Time} {w : Msg} (h : IsLast mem m false l s)
    (hw : mem.get? (m + 1) = some w) (hl : w.loc ≠ l) : IsLast mem m true l s := by
  obtain ⟨y, hy, hyl⟩ := h.msg
  refine ⟨h.gt, fun _ e => ?_, h.msg, fun s' z h1 _ hz => h.last s' z h1 Pf.of_false hz⟩
  subst e; rw [hw] at hy; cases hy; exact hl hyl

/-- **The fulfilment of `w`, replayed** (the end of phase A): the post-run
fulfils `m + 1`, the pre-run writes `w` fresh with the same constraining
view, which is at most `m`. -/
theorem write_trans_psim {M : Memory} {w : Msg} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.PSim M tid w true B c') (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htr' : ∀ a, tr' = some a → a ≤ c'.mem.last)
    {extra extra' : View} (hex : VR M.last extra extra') (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr')
    (hwl : w.loc = l) (hwv : w.val = v) (hwt : w.tid = tid) (hok : WriteOk A tid iv c k l tr extra (M.last + 1)) :
    ∃ c2' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr',
      (afterWrite A iv c (A.storeKind k) xcl l v (M.last + 1) (max iv.addrR (max iv.dataR extra)) true xr).PSim
        M tid w false B c2' := by
  have hrel := hs.rel.views
  have hB := (writePre_vr A hrel hiv k hex).max (hrel.coh l)
  have hML := hs.memP.last_le
  have hbt : max (writePre A iv c k extra) (c.views.getCoh l) ≤ M.last := by have := hok.1; omega_t
  have hbe := hB.eq hbt
  have hok' : WriteOk A tid iv' c' k l tr' extra' (c'.mem.last + 1) := by
    refine ⟨by rw [hbe]; omega_t, fun a ha => ⟨by have := htr' a ha; omega_t, ?_⟩⟩
    cases tr with
    | none => cases tr' <;> simp only [OptR] at htr; cases ha
    | some r =>
      cases tr' with
      | none => exact htr.elim
      | some a' =>
        cases ha
        exact hs.atomic htr (fun _ => (hok.2 r rfl).2) (by omega_t)
  have hmem := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
    (extra := extra') (xr := xr')).mpr (Or.inr ⟨hok', rfl⟩)
  refine ⟨_, hmem, ?_⟩
  have hxw : ({ loc := l, val := v, tid } : Msg) = w := by
    cases w; simp only at hwl hwv hwt; subst hwl hwv hwt; rfl
  have hwq := hs.outW rfl
  have hnot' : c'.mem.last + 1 ∉ c'.prom := fun h => by have := hs.promLe _ h; omega_t
  have hnotm : M.last + 1 ∉ c'.prom := fun h => by have := hs.promLe _ h; omega_t
  have hpe' : (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) = c'.prom := by
    rw [List.erase_append_right _ hnot']; simp
  have hpe : c.prom.erase (M.last + 1) = c'.prom := by
    rw [hs.promEq]; unfold outL; simp only [↓reduceIte]
    rw [List.erase_append_right _ hnotm]; simp
  have hfl : c'.prom.filter (· ≤ M.last) = c'.prom :=
    List.filter_eq_self.mpr fun s h => by simpa using hs.promLe s h
  -- no performed post-write to `l` above `m`: the fulfilment needs `coh l ≤ m`
  have hnoW : ∀ s y, M.last < s → s ≠ M.last + 1 → c.mem.get? s = some y → y.loc ≠ l := by
    intro s y h1 h2 hy hyl
    have := hs.ownR s y h1 (fun _ => h2) hy
    rw [hyl] at this
    have := Nat.le_max_right (writePre A iv c k extra) (c.views.getCoh l)
    omega_t
  have hlastW : IsLast c.mem M.last false l (M.last + 1) :=
    ⟨by omega_t, Pf.of_false, ⟨w, hwq, hwl⟩, fun s' y h1 _ hy => hnoW s' y (by omega_t) (by omega_t) hy⟩
  have hgetq : ∀ s y, c'.mem.get? s = some y → (c'.mem.append { loc := l, val := v, tid }).1.get? s = some y :=
    fun s y h => by rw [Memory.get?_append_of_le _ _ _ (c'.mem.last_le_of_get?_eq_some h)]; exact h
  exact
    { rel := by
        refine afterWrite_rel A ?_ hiv.addrW _ _ _ _ (VR.of_gt (by omega_t) (by omega_t))
          (hiv.addrR.max (hiv.dataR.max hex)) _ _ hxr ?_ hs.rel.loadViews hs.rel.rmwWrote hs.rel.stores
        · exact hrel
        · show (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) = (c.prom.erase (M.last + 1)).filter _
          rw [hpe', hpe, hfl]
      promEq := by
        show c.prom.erase (M.last + 1) = (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) ++ outL M.last false
        rw [hpe, hpe']; simp [outL]
      promLe := by show ∀ s ∈ (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1), _; rw [hpe']; exact hs.promLe
      memR := hs.memR
      memP := hs.memP.trans (Memory.Prefix.append _ _)
      outW := fun h => Bool.noConfusion h
      tidR := hs.tidR
      tidP := fun u y hu hy => by
        rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
        · exact hs.tidP u y hu hy'
        · rfl
      ownR := fun u y hu _ hy => by
        rw [afterWrite_getCoh]
        by_cases e : u = M.last + 1
        · subst e
          have hy' : c.mem.get? (M.last + 1) = some y := hy
          rw [hwq] at hy'; cases hy'
          simp only [hwl, ↓reduceIte]; exact Nat.le_max_right _ _
        · have := hs.ownR u y hu (fun _ => e) hy
          split
          · rename_i e'; rw [e'] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
          · exact this
      fwdR := fun l' f hf hm => by
        rw [afterWrite_getFwd] at hf
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf
          subst hf
          exact hlastW
        · simp only [e, ↓reduceIte] at hf
          exact (hs.fwdR l' f hf hm).unout hwq (by rw [hwl]; exact fun h => e h.symm)
      fwdP := fun l' f hf hm => by
        rw [afterWrite_getFwd] at hf
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf
          subst hf
          exact IsLast.append_new _ hML Pf.of_false
        · simp only [e, ↓reduceIte] at hf
          exact (hs.fwdP l' f hf hm).append_ne (fun h => e h.symm)
      lat :=
        { fwd := fun l' s y hl hy => by
            by_cases e : l = l'
            · subst e
              have := hl.unique hlastW
              subst this
              have hy' : c.mem.get? (M.last + 1) = some y := hy
              rw [hwq] at hy'; cases hy'
              refine ⟨c'.mem.last + 1, IsLast.append_new _ hML Pf.of_false, ?_⟩
              show (c'.mem.append _).1.get? _ = _
              rw [Memory.get?_append_last, hxw]
            · obtain ⟨s', h1, h2⟩ := hs.lat.fwd l' s y (hl.toOut hwq (by rw [hwl]; exact e)) hy
              exact ⟨s', h1.append_ne e, hgetq s' y h2⟩
          back := fun u y hu hy => by
            rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
            · obtain ⟨s, z, h1, -, h3, h4⟩ := hs.lat.back u y hu hy'
              exact ⟨s, z, h1, Pf.of_false, h3, h4⟩
            · exact ⟨M.last + 1, w, by omega_t, Pf.of_false, hwq, hwl⟩ }
      bnd := (writeSuccs_bnd A tid iv' hs.bnd hiv' hex' hmem).1
      pnow := fun _ => .inr ⟨max (writePre A iv' c' k extra') (c'.views.getCoh l), by rw [hbe]; exact hbt, List.mem_append_right _ (by rw [hxw]; exact List.mem_singleton_self _)⟩ }

/-! ## One write -/

/-- **One write, replayed**: a fulfilment at or below `m` by the same
fulfilment, the fulfilment of `w` by its fresh write (phase A ends), a fresh
write by a fresh write. -/
theorem writeSuccs_psim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.PSim M tid w out B c') (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htr' : ∀ a, tr' = some a → a ≤ c'.mem.last)
    {extra extra' : View} (hex : VR M.last extra extra') (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr') {c2 : Ctx}
    (h : c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    ∃ c2' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr', ∃ out2, c2.PSim M tid w out2 B c2' ∧
      (out = false → out2 = false) := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, htp, y, hy, hyl, hyv, hyt, hok, rfl⟩ | ⟨hok, rfl⟩
  · by_cases htm : t ≤ M.last
    · obtain ⟨c2', h1, h2⟩ := write_ful_psim A tid hs hiv hiv' htr hex hex' hxr htp hy hyl hyv hyt hok htm
      exact ⟨c2', h1, out, h2, id⟩
    · have hto : out = true ∧ t = M.last + 1 := by
        rw [hs.promEq, List.mem_append] at htp
        rcases htp with h | h
        · have := hs.promLe t h; omega_t
        · unfold outL at h; split at h
          · rename_i ho; exact ⟨ho, List.mem_singleton.mp h⟩
          · cases h
      obtain ⟨rfl, rfl⟩ := hto
      have hwy : y = w := by rw [hs.outW rfl] at hy; exact (Option.some.inj hy).symm
      subst hwy
      obtain ⟨c2', h1, h2⟩ := write_trans_psim A tid hs hiv hiv' htr htr' hex hex' hxr hyl hyv hyt hok
      exact ⟨c2', h1, false, h2, fun _ => rfl⟩
  · obtain ⟨c2', h1, h2⟩ := write_now_psim A tid (xcl := xcl) (v := v) hs hiv hiv' htr htr' hex hex' hxr hok
    exact ⟨c2', h1, out, h2, id⟩

end Rules

/-! ## Memory-silent steps: fences, the RMW post-processing, a failing exclusive -/

/-- A step that keeps coherence, forwarding, memory, promises, load views and
the pre-run's promised writes on both sides keeps the simulation, given
related views. -/
theorem _root_.Kraken.Promising.Ctx.PSim.congr {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {B : Prop}
    {c c' c2 c2' : Ctx} (hs : c.PSim M tid w out B c')
    (hv : c2.views.Rel M.last c2'.views) (hcoh : ∀ l, c2.views.getCoh l = c.views.getCoh l)
    (hf : ∀ l, c2.views.getFwd l = c.views.getFwd l) (hf' : ∀ l, c2'.views.getFwd l = c'.views.getFwd l)
    (hm : c2.mem = c.mem) (hm' : c2'.mem = c'.mem) (hp : c2.prom = c.prom) (hp' : c2'.prom = c'.prom)
    (hlv : c2.loadViews = c.loadViews) (hlv' : c2'.loadViews = c'.loadViews)
    (hsv : VR M.last c2.succView c2'.succView) (hrw : c2.rmwWrote = c2'.rmwWrote) (hst : c2.stores = c2'.stores)
    (hb : c2'.Bnd) (hpn : c2'.promisedNow = c'.promisedNow) : c2.PSim M tid w out B c2' :=
  { rel := ⟨hv, by rw [hp, hp', hs.rel.prom], by rw [hlv, hlv']; exact hs.rel.loadViews, hsv, hrw, hst⟩
    promEq := by rw [hp, hp']; exact hs.promEq
    promLe := by rw [hp']; exact hs.promLe
    memR := hm ▸ hs.memR
    memP := hm' ▸ hs.memP
    outW := by rw [hm]; exact hs.outW
    tidR := by rw [hm]; exact hs.tidR
    tidP := by rw [hm']; exact hs.tidP
    ownR := by rw [hm]; intro u x h1 h2 hx; rw [hcoh]; exact hs.ownR u x h1 h2 hx
    fwdR := by rw [hm]; intro l f h; rw [hf] at h; exact hs.fwdR l f h
    fwdP := by rw [hm']; intro l f h; rw [hf'] at h; exact hs.fwdP l f h
    lat := by rw [hm, hm']; exact hs.lat
    bnd := hb
    pnow := by rw [hpn]; exact hs.pnow }

section Silent

variable {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {B : Prop} {c c' : Ctx}

theorem fenceStep_psim (hs : c.PSim M tid w out B c') (k : FenceKind) :
    (fenceStep c k).PSim M tid w out B (fenceStep c' k) := by
  have hv := hs.rel.views
  have hb := fenceStep_bnd hs.bnd k
  have hpn := fenceStep_promisedNow c' k
  cases k
  · exact hs.congr (hv.setNew (hv.vrNew.max ((hv.vrOld.max hv.vrOldNR).max (hv.vwOld.max hv.vwOldNT)))
      (hv.vwNew.max ((hv.vrOld.max hv.vrOldNR).max (hv.vwOld.max hv.vwOldNT))))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb hpn
  · exact hs.congr (hv.setNew (hv.vrNew.max hv.vrOld) (hv.vwNew.max hv.vrOld))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb hpn
  · exact hs.congr (hv.setNew hv.vrNew (hv.vwNew.max (hv.vwOld.max hv.vwOldNT)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb hpn
  · exact hs.congr (hv.setNew (hv.vrNew.max (hv.vwOld.max hv.vwOldNT)) (hv.vwNew.max (hv.vwOld.max hv.vwOldNT)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb hpn
  · exact hs.congr (hv.setNew (hv.vrNew.max hv.vCAP) hv.vwNew)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb hpn

theorem fenceOpt_psim (hs : c.PSim M tid w out B c') (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).PSim M tid w out B (if b then fenceStep c' k else c') := by
  cases b
  · exact hs
  · exact fenceStep_psim hs k

theorem rmwPost_psim (A : Arch) (hs : c.PSim M tid w out B c') (k : RmwKind) (noRet : Bool) (l : Loc) :
    (rmwPost A k noRet l c).PSim M tid w out B (rmwPost A k noRet l c') := by
  have hv := hs.rel.views
  have hb := (rmwPost_bnd A hs.bnd k noRet l).1
  revert hb
  unfold rmwPost
  by_cases hk : (A.rmwKind k == .acqRel && !noRet) = true
  · simp only [hk, ↓reduceIte]
    intro hb
    exact hs.congr (hv.setNew (hv.vrNew.max (hv.coh l)) (hv.vwNew.max (hv.coh l)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      rfl hs.rel.stores hb rfl
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    intro hb
    exact hs.congr hv (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl
      hs.rel.succView rfl hs.rel.stores hb rfl

theorem xclFail_psim (hs : c.PSim M tid w out B c') (l : Loc) :
    Ctx.PSim M tid w out B
      { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
      { c' with views := { c'.views with xclb := none }, succView := 0, log := c'.log ++ [.xclFail l] } :=
  hs.congr hs.rel.views.xclbNone (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl
    (VR.refl _ _) hs.rel.rmwWrote hs.rel.stores ⟨hs.bnd.views.xclbNone, hs.bnd.loadViews, Nat.zero_le _⟩ rfl

end Silent

/-! ## One instruction's event tree -/

section Rules

variable (A : Arch) (tid : Nat)

private theorem getLastD_le {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) :
    ∀ d, d ≤ n → xs.getLastD d ≤ n := by
  induction xs with
  | nil => intro d hd; exact hd
  | cons x xs ih =>
    intro _ _
    rw [List.getLastD_cons]
    exact ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν)) x (h x List.mem_cons_self)

/-- **One instruction's event tree, replayed.** A run of the event tree from
the post-context is matched by a run from the pre-context, ending in
simulating contexts; phase A may end inside the tree (at the fulfilment of
`w`), never restart. -/
theorem runTree_psim {σ : Type} {M : Memory} {w : Msg} {B : Prop} {iv iv' : InstrViews} (hiv : iv.Rel M.last iv')
    (tree : EvTree σ) :
    ∀ (out : Bool) (c c' : Ctx) (s : σ) (c2 : Ctx), c.PSim M tid w out B c' → iv'.Le c'.mem.last →
      .ok (s, c2) ∈ runTree A tid iv c tree →
      ∃ c2' out2, .ok (s, c2') ∈ runTree A tid iv' c' tree ∧ c2.PSim M tid w out2 B c2' ∧
        (out = false → out2 = false) := by
  induction tree with
  | done s0 =>
    intro out c c' s c2 hs _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c', out, by simp [runTree], hs, id⟩
  | fault msg =>
    intro out c c' s c2 _ _ h
    simp [runTree] at h
  | choose n k ih =>
    intro out c c' s c2 hs hiv' h
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨c2', out2, h', hs', ho⟩ := ih i out c c' s c2 hs hiv' h
    exact ⟨c2', out2, ⟨i, hi, h'⟩, hs', ho⟩
  | load k xcl l ret ih =>
    intro out c c' s c2 hs hiv' h
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t, v, c0⟩, hx, h⟩ := h
    obtain ⟨⟨t', v', c0'⟩, hx', hv, -, -, hsim⟩ := readSuccs_psim A tid hs hiv hiv' hx
    simp only at hv
    have hm0 : c0'.mem = c'.mem := (readSuccs_mp A iv' hx').1
    obtain ⟨c2', out2, h', hs', ho⟩ := ih v out c0 c0' s c2 hsim (hm0 ▸ hiv') h
    exact ⟨c2', out2, ⟨(t', v', c0'), hx', by rw [hv]; exact h'⟩, hs', ho⟩
  | store k xcl l v ret ih =>
    intro out c c' s c2 hs hiv' h
    have hv := hs.rel.views
    have htr : OptR M.last (if xcl then c.views.xclb.map (·.1) else none)
        (if xcl then c'.views.xclb.map (·.1) else none) := by
      cases xcl
      · trivial
      · have hx := hv.xclb
        revert hx
        rcases c.views.xclb with _ | ⟨a, b, l1⟩ <;> rcases c'.views.xclb with _ | ⟨a', b', l2⟩ <;>
          simp only [XclbR, OptR, Option.map, imp_self, ↓reduceIte]
        rintro ⟨h1, -, -⟩; exact h1
    have htr' : ∀ a, (if xcl then c'.views.xclb.map (·.1) else none) = some a → a ≤ c'.mem.last := by
      intro a ha
      cases xcl
      · cases ha
      · simp only [↓reduceIte] at ha
        cases hx : c'.views.xclb with
        | none => rw [hx] at ha; cases ha
        | some p =>
          rw [hx] at ha
          obtain ⟨a0, b0, l0⟩ := p
          simp only [Option.map_some, Option.some.injEq] at ha
          subst ha
          exact (hs.bnd.views.xclb _ _ _ hx).1
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨hp, c0, hc0, h⟩ := h
      have hivs : (iv.forStore c.stores).Rel M.last (iv'.forStore c'.stores) :=
        hs.rel.stores ▸ hiv.forStore c.stores
      obtain ⟨c0', hc0', out1, hsim, ho1⟩ := writeSuccs_psim A tid hs hivs (hiv'.forStore c'.stores) htr htr'
        (VR.refl _ 0) (Nat.zero_le _) (xr' := if xcl then (c'.views.xclb.map (·.2.1)).getD 0 else 0)
        (VR.ite hs.rel.views.xclb.xclRead (VR.refl _ _)) hc0
      have hl := (writeSuccs_bnd A tid _ hs.bnd (hiv'.forStore c'.stores) (Nat.zero_le _) hc0').2
      obtain ⟨c2', out2, h', hs', ho2⟩ := ih true out1 c0 c0' s c2 hsim (hiv'.mono hl) h
      refine ⟨c2', out2, Or.inl ?_, hs', fun e => ho2 (ho1 e)⟩
      rw [List.mem_ite_nil_left, List.mem_flatMap]
      refine ⟨?_, c0', hc0', h'⟩
      have hx := hv.xclb
      revert hp hx
      generalize c.views.xclb = a
      generalize c'.views.xclb = b
      rcases a with _ | ⟨a1, a2, l1⟩ <;> rcases b with _ | ⟨b1, b2, l2⟩ <;> intro hp hx
      · exact hp
      · exact (hx : False).elim
      · exact (hx : False).elim
      · obtain ⟨-, -, rfl⟩ := hx; exact hp
    · rw [List.mem_ite_nil_right] at h
      obtain ⟨c2', out2, h', hs', ho⟩ := ih false out _ _ s c2 (xclFail_psim hs l) hiv' h.2
      refine ⟨c2', out2, Or.inr ?_, hs', ho⟩
      rw [List.mem_ite_nil_right]
      exact ⟨h.1, h'⟩
  | fence k ret ih =>
    intro out c c' s c2 hs hiv' h
    simp only [runTree] at h ⊢
    exact ih () out _ _ s c2 (fenceStep_psim hs k) (by rw [fenceStep_mem]; exact hiv') h
  | rmw k noRet l op ret ih =>
    intro out c c' s c2 hs hiv' h
    simp only [runTree] at h ⊢
    have hs1 := fenceOpt_psim hs A.rmwFence .sy
    have hm1 : (if A.rmwFence then fenceStep c' .sy else c').mem = c'.mem := by
      split <;> simp only [fenceStep_mem]
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hs1
    generalize (if A.rmwFence then fenceStep c' .sy else c') = c1' at hs1 hm1 ⊢
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c3⟩, hx, h⟩ := h
    simp only at h
    obtain ⟨⟨tr', old', c3'⟩, hx', hv, htr, htrl, hsim⟩ := readSuccs_psim A tid hs1 hiv (hm1 ▸ hiv') hx
    simp only at hv htr htrl
    have hm3 : c3'.mem = c1'.mem := (readSuccs_mp A iv' hx').1
    split at h
    · rename_i hop
      obtain ⟨c2', out2, h', hs', ho⟩ := ih old out _ _ s c2 (fenceOpt_psim hsim A.rmwFence .sy)
        (by split <;> simp only [fenceStep_mem, hm3, hm1] <;> exact hiv') h
      refine ⟨c2', out2, List.mem_flatMap.mpr ⟨(tr', old', c3'), hx', ?_⟩, hs', ho⟩
      simp only [hv, hop]
      exact h'
    · rename_i new hop
      rw [List.mem_flatMap] at h
      obtain ⟨c4, hc4, h⟩ := h
      change .ok (s, c2) ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c4) .sy else rmwPost A k noRet l c4) (ret old) at h
      have hiv3 : iv'.Le c3'.mem.last := by rw [hm3, hm1]; exact hiv'
      obtain ⟨c4', hc4', out1, hsim4, ho1⟩ := writeSuccs_psim A tid hsim hiv hiv3 (tr := some tr) (tr' := some tr')
        htr (fun a ha => by cases ha; rw [hm3]; exact htrl) (clampL_getLastD hsim.rel.loadViews)
        (getLastD_le hsim.bnd.loadViews 0 (Nat.zero_le _)) (VR.refl _ 0) hc4
      have hl := (writeSuccs_bnd A tid iv' hsim.bnd hiv3 (getLastD_le hsim.bnd.loadViews 0 (Nat.zero_le _)) hc4').2
      have hm5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c4') .sy else rmwPost A k noRet l c4').mem =
          c4'.mem := by
        split <;> simp only [fenceStep_mem, rmwPost_mem]
      obtain ⟨c2', out2, h', hs', ho2⟩ := ih old out1 _ _ s c2
        (fenceOpt_psim (rmwPost_psim A hsim4 k noRet l) A.rmwFence .sy) (by rw [hm5]; exact hiv3.mono hl) h
      refine ⟨c2', out2, List.mem_flatMap.mpr ⟨(tr', old', c3'), hx', ?_⟩, hs', fun e => ho2 (ho1 e)⟩
      simp only [hv, hop, List.mem_flatMap]
      exact ⟨c4', hc4', h'⟩

end Rules

/-! ## Threads -/

/-- **The post-run thread `t` against `mem` and the pre-run thread `t'`
against `mem'`**: the thread-level form of `Ctx.PSim`. -/
structure _root_.Kraken.Promising.Thread.PSim (M : Memory) (tid : Nat) (w : Msg) (out : Bool) (t : Thread I)
    (mem : Memory) (t' : Thread I) (mem' : Memory) : Prop where
  rel : t.Rel M.last t'
  promEq : t.prom = t'.prom ++ outL M.last out
  promLe : ∀ s ∈ t'.prom, s ≤ M.last
  memR : M.Prefix mem
  memP : M.Prefix mem'
  outW : out = true → mem.get? (M.last + 1) = some w
  tidR : ∀ u x, M.last < u → mem.get? u = some x → x.tid = tid
  tidP : ∀ u x, M.last < u → mem'.get? u = some x → x.tid = tid
  ownR : ∀ u x, M.last < u → Pf M.last out u → mem.get? u = some x → u ≤ t.views.getCoh x.loc
  fwdR : FwdLast mem M.last out t.views
  fwdP : FwdLast mem' M.last false t'.views
  lat : LatRel M.last out mem mem'
  bnd : t'.Bnd mem'.last

/-- The initial contexts of an instruction of simulating threads. -/
theorem _root_.Kraken.Promising.Thread.PSim.ctx {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {t t' : Thread I}
    {mem mem' : Memory} (hs : t.PSim M tid w out mem t' mem') (log : List TraceEv) :
    Ctx.PSim M tid w out (out = false) { views := t.views, prom := t.prom, mem, log }
      { views := t'.views, prom := t'.prom, mem := mem', log } :=
  { rel := ⟨hs.rel.views, hs.rel.prom, rfl, VR.refl _ _, rfl, rfl⟩
    promEq := hs.promEq
    promLe := hs.promLe
    memR := hs.memR
    memP := hs.memP
    outW := hs.outW
    tidR := hs.tidR
    tidP := hs.tidP
    ownR := hs.ownR
    fwdR := hs.fwdR
    fwdP := hs.fwdP
    lat := hs.lat
    bnd := ⟨hs.bnd.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
    pnow := fun h => .inl h }

/-- **One instruction, replayed.** An instruction of the post-run thread is
matched by an instruction of the pre-run thread, ending in simulating
threads. If phase A ends during the instruction, the pre-run's instruction
writes `w` as "promise now" with a constraining view at most `|M|`. -/
theorem stepOne_psim (A : Arch) {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {t t' : Thread I}
    {mem mem' : Memory} (hs : t.PSim M tid w out mem t' mem')
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ outs' o' out2, stepOne A t' tid mem' = some outs' ∧ .ok o' ∈ outs' ∧
      o.thread.PSim M tid w out2 o.mem o'.thread o'.mem ∧ (out = false → out2 = false) ∧
      (out = true → out2 = false → ∃ ν, ν ≤ M.last ∧ (w, ν) ∈ o'.promisedNow) := by
  unfold stepOne at hstep ⊢
  rw [← hs.rel.st]
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c2⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      have hiv := instrViews_rel hs.rel (I.deps t.st)
      have hiv' := instrViews_le hs.bnd.regs (I.deps t.st)
      have hc := hs.ctx [.instr tid (I.showInstr t.st)]
      obtain ⟨c2', out2, hr', hs2, ho2⟩ := runTree_psim A tid hiv tree out _ _ st c2 hc hiv' hr
      obtain ⟨hcb, hl⟩ := runTree_bnd A tid _ tree _ st c2' hc.bnd hiv' hr'
      obtain ⟨th', hth', hrel⟩ := finishInstr_rel hs.rel hs2.rel hiv th hth
      obtain ⟨hp', hv'⟩ := finishInstr_relKey hth'
      refine ⟨_, _, out2, rfl, List.mem_flatMap.mpr ⟨.ok (st, c2'), hr', List.mem_map.mpr ⟨th', hth', rfl⟩⟩,
        ?_, ho2, fun h1 h2 => ?_⟩
      · have e1 := Views.getCoh_congr hv
        have e2 := Views.getFwd_congr hv
        have e2' := Views.getFwd_congr hv'
        exact
          { rel := hrel
            promEq := by rw [hp, hp']; exact hs2.promEq
            promLe := by rw [hp']; exact hs2.promLe
            memR := hs2.memR
            memP := hs2.memP
            outW := hs2.outW
            tidR := hs2.tidR
            tidP := hs2.tidP
            ownR := fun u x h1 h2 hx => by rw [e1]; exact hs2.ownR u x h1 h2 hx
            fwdR := fun l f h => by rw [e2] at h; exact hs2.fwdR l f h
            fwdP := fun l f h => by rw [e2'] at h; exact hs2.fwdP l f h
            lat := hs2.lat
            bnd := finishInstr_bnd hcb.views hcb.loadViews hcb.succView (hiv'.mono hl) (hs.bnd.regs.mono hl) th' hth' }
      · rcases hs2.pnow h2 with h | h
        · rw [h1] at h; cases h
        · exact h

end Kraken.Promising.Proj
