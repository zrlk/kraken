/-
**Lemma 1's replay direction, the simulation**
(used by `PromReplay.lean`). ISA-neutral and architecture-neutral; executable
`Thread` rules only.

A run of the thread from `(t, M)` that writes `w` as "promise now" with a
constraining view `ν ≤ |M|` (the *original*, a `CertWriteN` run) is replayed
step by step by a run of the thread after promising `w` at `|M| + 1`, against
`M ++ [w]` (the *replay*). The relation is the promise projection's `Ctx.PSim`/`Thread.PSim`
(`PromProjectionSim.lean`), unchanged and in the same orientation (first
argument the thread with the promise), wrapped in `Ctx.RSim`/`Thread.RSim`,
which add what the backward direction needs:
- `ownP`: the original's own messages above `m = |M|` are at most its `coh`
  of their location;
- `xclP`: a pending load exclusive of the original above `m` is at most its
  `coh` of the location;
- `bndR`: the replay is bounded;
- `fresh`: while `w` is outstanding the original has not yet written `w`
  with a constraining view `≤ m` in this instruction.

While `w` is outstanding (`out`), the original's fresh write of `w` with
constraining view `≤ m` is replayed as the fulfilment of `m + 1`
(`write_conv_rsim`, phase A ends); every other fresh write is replayed fresh,
a fulfilment by the same fulfilment, a read by a read of the same value. The
replay must never see the outstanding `w` in the window of a read of
`w.loc`; this holds because the original's `coh w.loc` stays `≤ m` until it
writes `w` (`ν ≤ m` and `coh` only grows). That is information about the
*future* of the original run, so `runTree_rsim` and `stepOne_rsim` take it as
a hypothesis on the instruction's final context (`FutOk`), and
`runTree_pnD` carries it back to each read.

Contents:
- `Ctx.RSim`, `IsLast.exists_of`, `Ctx.RSim.atomic`;
- `readSuccs_rsim`; `write_now_rsim`, `write_ful_rsim`, `write_conv_rsim`,
  `writeSuccs_rsim`; `fenceStep_rsim`, `rmwPost_rsim`, `xclFail_rsim`;
- `PnBound`, `PnD`, `runTree_pnD`, `FutOk`, `fut_back`; `runTree_rsim`;
- `Views.Rel.symm`, `InstrViews.Rel.symm`, `finishInstr_withProm`,
  `finishInstr_rel_back`; `Thread.RSim`, `stepOne_cohLe`, `stepOne_rsim`.
-/
import Kraken.Promising.PromProjectionSim
import Kraken.Promising.LiveWfProm

namespace Kraken.Promising.Proj

open Kraken.Promising

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **The replay relation** (Lemma 1, replay direction): `c` is the replay
(the thread with `w` promised at `|M| + 1`), `c'` the original run (which
writes `w` as "promise now"). `PSim` in the same orientation as Q3, plus the
facts the backward direction needs (module docstring). -/
structure _root_.Kraken.Promising.Ctx.RSim (M : Memory) (tid : Nat) (w : Msg) (out : Bool) (B : Prop) (c c' : Ctx) :
    Prop where
  ps : c.PSim M tid w out B c'
  ownP : ∀ u x, M.last < u → c'.mem.get? u = some x → u ≤ c'.views.getCoh x.loc
  xclP : ∀ a ν l, c'.views.xclb = some (a, ν, l) → M.last < a → a ≤ c'.views.getCoh l
  bndR : c.Bnd
  fresh : out = true → ∀ ν, ν ≤ M.last → (w, ν) ∉ c'.promisedNow

/-- A performed message to `l` above `m` gives a last one. -/
theorem IsLast.exists_of {mem : Memory} {m : Nat} {out : Bool} {l : Loc} :
    ∀ (d : Nat) (u : Time) (x : Msg), mem.last - u = d → m < u → Pf m out u → mem.get? u = some x → x.loc = l →
      ∃ s, IsLast mem m out l s := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro u x hd hu hp hx hl
    by_cases hex : ∃ s' y, u < s' ∧ Pf m out s' ∧ mem.get? s' = some y ∧ y.loc = l
    · obtain ⟨s', y, h1, h2, h3, h4⟩ := hex
      have := mem.last_le_of_get?_eq_some h3
      exact ih (mem.last - s') (by omega_t) s' y rfl (by omega_t) h2 h3 h4
    · exact ⟨u, ⟨hu, hp, ⟨x, hx, hl⟩, fun s' y h1 h2 h3 h4 => hex ⟨s', y, h1, h2, h3, h4⟩⟩⟩

/-- The replay's exclusive check passes: at or below `m` it sees what the
original saw (`hr`), above `m` only the thread's own messages. -/
theorem _root_.Kraken.Promising.Ctx.RSim.atomic {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {B : Prop}
    {c c' : Ctx} (hs : c.RSim M tid w out B c') {l : Loc} {a a' tq tp : Time} (hra : VR M.last a a')
    (hr : a' ≤ M.last → c'.mem.atomic l tid a' tq = true) (hq : M.last < tq) :
    c.mem.atomic l tid a tp = true := by
  have hps := hs.ps
  by_cases ham : a ≤ M.last
  · have e : a' = a := hra.eq ham
    subst e
    cases hrd : c.mem.read? l a' with
    | none => unfold Memory.atomic; rw [hrd]
    | some val =>
      have hrd0 : c'.mem.read? l a' = some val := by rw [hps.memP.read? ham, ← hps.memR.read? ham]; exact hrd
      apply Memory.atomic_of_forall
      intro u x h1 h2 hx hl
      by_cases hum : u ≤ M.last
      · rw [hps.memR.get? hum, ← hps.memP.get? hum] at hx
        exact Memory.atomic_elim (hr ham) hrd0 u x h1 (by omega_t) hx hl
      · exact hps.tidR u x (by omega_t) hx
  · apply Memory.atomic_of_forall
    intro u x h1 _ hx _
    exact hps.tidR u x (by omega_t) hx

section Rules

variable (A : Arch) (tid : Nat)

/-- **One read, replayed backwards.** A read of the original run is matched
by a read of the replay of the same value: the same timestamp at or below
`m`, else the last own write to the location (the same message). While `w`
is outstanding, a read of `w.loc` must leave the original's `coh w.loc` at
most `m` (`hfut`; from `ν ≤ |M|` and monotonicity of `coh`): otherwise the
replay would see the outstanding promise in the read's window. -/
theorem readSuccs_rsim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.RSim M tid w out B c') (hiv : iv.Rel M.last iv') (hivR : iv.Le c.mem.last) (hiv' : iv'.Le c'.mem.last)
    {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x' : Time × Val × Ctx}
    (hx' : x' ∈ readSuccs A iv' c' k xcl l noRet)
    (hfut : out = true → w.loc = l → x'.2.2.views.getCoh l ≤ M.last) :
    ∃ x ∈ readSuccs A iv c k xcl l noRet, x.2.1 = x'.2.1 ∧ VR M.last x.1 x'.1 ∧ x.1 ≤ c.mem.last ∧
      (M.last < x'.1 → x'.1 ≤ x'.2.2.views.getCoh l) ∧ x.2.2.RSim M tid w out B x'.2.2 := by
  obtain ⟨t', v, rfl, htl', hv', hw', hp'⟩ := (mem_readSuccs A).mp hx'
  have hps := hs.ps
  have hrel := hps.rel.views
  have hpre : VR M.last (readPre A iv c k) (readPre A iv' c' k) :=
    hiv.addrR.max (hrel.vrNew.max (VR.ite hrel.vRel (VR.refl _ _)))
  have hB : VR M.last (max (readPre A iv c k) (c.views.getCoh l)) (max (readPre A iv' c' k) (c'.views.getCoh l)) :=
    hpre.max (hrel.coh l)
  have hMR := hps.memR.last_le
  -- a write to `l` above `t'` in the original memory, within its bound, contradicts the read
  have hnw : ∀ u y, t' < u → u ≤ max (readPre A iv' c' k) (c'.views.getCoh l) → c'.mem.get? u = some y →
      y.loc = l → False := by
    intro u y h1 h2 hy hl
    rw [(Memory.writeIn_iff _ _ _ _).mpr ⟨u, y, h1, h2, hy, hl⟩] at hw'; cases hw'
  have hcoh' : c'.views.getCoh l ≤ max (readPre A iv' c' k) (c'.views.getCoh l) := Nat.le_max_right _ _
  -- the original's coherence view after the read is at least its bound
  have hfut' : out = true → w.loc = l → max (readPre A iv' c' k) (c'.views.getCoh l) ≤ M.last := by
    intro ho hl
    have h := hfut ho hl
    have h' : (c'.views.setCoh l (max (readPre A iv' c' k) (readView A (A.loadKind k) (c'.views.getFwd l) t'))).getCoh l
        ≤ M.last := h
    simp only [Views.getCoh_setCoh, ↓reduceIte] at h'
    omega_t
  obtain ⟨t, htl, hv, hw, hp, ht, hiff⟩ : ∃ t, t ≤ c.mem.last ∧ c.mem.read? l t = some v ∧
      c.mem.writeIn l t (max (readPre A iv c k) (c.views.getCoh l)) = false ∧
      c.prom.contains t = false ∧ VR M.last t t' ∧
      ∀ f g, c.views.getFwd l = some f → c'.views.getFwd l = some g → (f.time = t ↔ g.time = t') := by
    by_cases htm : t' ≤ M.last
    · refine ⟨t', by omega_t, by rw [hps.memR.read? htm, ← hps.memP.read? htm]; exact hv', ?_, ?_, VR.refl _ _, ?_⟩
      · rw [Bool.eq_false_iff, Ne, Memory.writeIn_iff]
        rintro ⟨u, y, h1, h2, hy, hl⟩
        by_cases hum : u ≤ M.last
        · rw [hps.memR.get? hum, ← hps.memP.get? hum] at hy
          refine hnw u y h1 ?_ hy hl
          by_cases hbm : max (readPre A iv c k) (c.views.getCoh l) ≤ M.last
          · rw [hB.eq hbm]; exact h2
          · have := hB.gt (by omega_t); omega_t
        · by_cases hpf : Pf M.last out u
          · obtain ⟨s, hlast⟩ := IsLast.exists_of _ u y rfl (by omega_t) hpf hy hl
            obtain ⟨z, hz, hzl⟩ := hlast.msg
            obtain ⟨s', hlast', hz'⟩ := hps.lat.fwd l s z hlast hz
            have h1' := hlast'.gt
            have := hs.ownP s' z h1' hz'
            exact hnw s' z (by omega_t) (Nat.le_trans this (hzl ▸ hcoh')) hz' hzl
          · -- the outstanding promise `w` at `m + 1`
            have ho : out = true := by
              cases ho : out
              · exact absurd Pf.of_false (ho ▸ hpf)
              · rfl
            have hu : u = M.last + 1 := by
              by_cases hne : u = M.last + 1
              · exact hne
              · exact absurd (fun _ => hne) hpf
            subst hu
            have hyw := hps.outW ho
            rw [hy] at hyw; cases hyw
            have := hfut' ho hl
            have := hB.gt (show M.last < max (readPre A iv c k) (c.views.getCoh l) by omega_t)
            omega_t
      · rw [Bool.eq_false_iff, Ne, List.contains_iff_mem]
        intro h
        rw [hps.promEq, List.mem_append] at h
        rcases h with h | h
        · rw [List.contains_iff_mem.mpr h] at hp'; cases hp'
        · unfold outL at h
          split at h
          · rw [List.mem_singleton] at h; omega_t
          · cases h
      · intro f g hf hg
        have hfg := hrel.fwd l
        rw [hf, hg] at hfg
        obtain ⟨h1, -, -⟩ := hfg
        constructor
        · intro e; rw [e] at h1; exact h1.eq htm
        · intro e; rw [e] at h1; exact h1.eq' htm
    · -- above `m`: the original reads its last own write to `l`
      rcases Memory.read?_eq_some _ hv' with ⟨rfl, -⟩ | ⟨y, hy, hyl, rfl⟩
      · omega_t
      have hlast' : IsLast c'.mem M.last false l t' :=
        ⟨by omega_t, Pf.of_false, ⟨y, hy, hyl⟩, fun s' z h1 _ hz hzl =>
          hnw s' z h1 (Nat.le_trans (hs.ownP s' z (by omega_t) hz) (hzl ▸ hcoh')) hz hzl⟩
      obtain ⟨s, z, hs1, hs2, hz, hzl⟩ := hps.lat.back t' y (by omega_t) hy
      obtain ⟨t, hlast⟩ := IsLast.exists_of _ s z rfl hs1 hs2 hz (hzl.trans hyl)
      obtain ⟨x, hx, hxl⟩ := hlast.msg
      obtain ⟨t2, hlast2, hx2⟩ := hps.lat.fwd l t x hlast hx
      have e2 := hlast2.unique hlast'
      subst e2
      rw [hy] at hx2; cases hx2
      refine ⟨t, c.mem.last_le_of_get?_eq_some hx, ?_, ?_, ?_, VR.of_gt hlast.gt (by omega_t), ?_⟩
      · rw [← hyl]; exact read?_of_get? hx (by have := hlast.gt; omega_t)
      · rw [Bool.eq_false_iff, Ne, Memory.writeIn_iff]
        rintro ⟨u, z, h1, -, hz, hzl⟩
        have hpu : Pf M.last out u := fun _ e => by have := hlast.gt; omega_t
        exact hlast.last u z h1 hpu hz hzl
      · rw [Bool.eq_false_iff, Ne, List.contains_iff_mem]
        intro h
        rw [hps.promEq, List.mem_append] at h
        rcases h with h | h
        · have := hps.promLe t h; have := hlast.gt; omega_t
        · unfold outL at h
          split at h
          · rename_i ho
            rw [List.mem_singleton] at h
            exact hlast.pf ho h
          · cases h
      · intro f g hf hg
        have hfg := hrel.fwd l
        rw [hf, hg] at hfg
        obtain ⟨h1, -, -⟩ := hfg
        constructor
        · intro e
          have hfm : M.last < f.time := by rw [e]; exact hlast.gt
          exact (hps.fwdP l g hg (h1.gt hfm)).unique hlast'
        · intro e
          have hgm : M.last < g.time := by rw [e]; omega_t
          exact (hps.fwdR l f hf (h1.gt' hgm)).unique hlast
  have hν : VR M.last (max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t))
      (max (readPre A iv' c' k) (readView A (A.loadKind k) (c'.views.getFwd l) t')) :=
    hpre.max (readView_vr A (hrel.fwd l) ht hiff)
  have hx := (mem_readSuccs A (iv := iv) (c := c) (k := k) (xcl := xcl) (l := l) (noRet := noRet)
    (x := (t, v, readNext A iv c k xcl l noRet t v))).mpr ⟨t, v, rfl, htl, hv, hw, hp⟩
  have hcohle' : ∀ l', c'.views.getCoh l' ≤ (readNext A iv' c' k xcl l noRet t' v).views.getCoh l' :=
    fun l' => Views.getCoh_le_setCoh _ _ _ _
  -- an original read above `m` reads an own message, at most `coh`
  have hown : M.last < t' → t' ≤ c'.views.getCoh l := by
    intro htm
    rcases Memory.read?_eq_some _ hv' with ⟨rfl, -⟩ | ⟨y, hy, hyl, -⟩
    · omega_t
    · have := hs.ownP t' y htm hy; rw [hyl] at this; exact this
  refine ⟨_, hx, rfl, ht, htl, fun h => Nat.le_trans (hown h) (hcohle' l), ?_⟩
  have hbR := (readSuccs_bnd A iv hs.bndR hivR hx).1
  have hb' := (readSuccs_bnd A iv' hps.bnd hiv' hx').1
  have hcohle : ∀ l', c.views.getCoh l' ≤ (readNext A iv c k xcl l noRet t v).views.getCoh l' :=
    fun l' => Views.getCoh_le_setCoh _ _ _ _
  exact
    { ps :=
        { rel := ⟨Views.Rel.read hrel hν hiv.addrW ht, hps.rel.prom, clampL_append hps.rel.loadViews hν,
            hps.rel.succView, hps.rel.rmwWrote, hps.rel.stores⟩
          promEq := hps.promEq
          promLe := hps.promLe
          memR := hps.memR
          memP := hps.memP
          outW := hps.outW
          tidR := hps.tidR
          tidP := hps.tidP
          ownR := fun u y h1 h2 hy => Nat.le_trans (hps.ownR u y h1 h2 hy) (hcohle _)
          fwdR := hps.fwdR
          fwdP := hps.fwdP
          lat := hps.lat
          bnd := hb'
          pnow := hps.pnow }
      ownP := fun u y h1 hy => Nat.le_trans (hs.ownP u y h1 hy) (hcohle' _)
      xclP := fun a ν l1 hx h1 => by
        show a ≤ (readNext A iv' c' k xcl l noRet t' v).views.getCoh l1
        have hx1 : (if xcl then some (t', max (readPre A iv' c' k) (readView A (A.loadKind k) (c'.views.getFwd l) t'), l)
            else c'.views.xclb) = some (a, ν, l1) := hx
        split at hx1
        · cases hx1; exact Nat.le_trans (hown h1) (hcohle' _)
        · exact Nat.le_trans (hs.xclP a ν l1 hx1 h1) (hcohle' _)
      bndR := hbR
      fresh := hs.fresh }

/-- **The fresh write of `w`, replayed as the fulfilment of `m + 1`** (the
end of phase A, backwards): the original appends `w` with constraining view
`≤ m`, the replay fulfils its outstanding promise. `htrP`: the paired read of
an exclusive/RMW write, if above `m`, is at most the original's `coh l`
(so it is at most `m`). -/
theorem write_conv_rsim {M : Memory} {w : Msg} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.RSim M tid w true B c') (hiv : iv.Rel M.last iv') (hivR : iv.Le c.mem.last) (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htrP : ∀ a, tr' = some a → M.last < a → a ≤ c'.views.getCoh l)
    {extra extra' : View} (hex : VR M.last extra extra') (hexR : extra ≤ c.mem.last) (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr')
    (hwl : w.loc = l) (hwv : w.val = v) (hwt : w.tid = tid)
    (hok' : WriteOk A tid iv' c' k l tr' extra' (c'.mem.last + 1))
    (hν : max (writePre A iv' c' k extra') (c'.views.getCoh l) ≤ M.last) :
    ∃ c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr,
      c2.RSim M tid w false B
        (afterWrite A iv'
          { c' with mem := (c'.mem.append { loc := l, val := v, tid }).1,
                    prom := c'.prom ++ [c'.mem.last + 1],
                    promisedNow := c'.promisedNow ++
                      [({ loc := l, val := v, tid }, max (writePre A iv' c' k extra') (c'.views.getCoh l))] }
          (A.storeKind k) xcl l v (c'.mem.last + 1) (max iv'.addrR (max iv'.dataR extra')) false xr') := by
  have hps := hs.ps
  have hrel := hps.rel.views
  have hB := (writePre_vr A hrel hiv k hex).max (hrel.coh l)
  have hML := hps.memP.last_le
  have hMR := hps.memR.last_le
  have hbe := hB.eq' hν
  have hbt : max (writePre A iv c k extra) (c.views.getCoh l) ≤ M.last := by rw [hbe]; exact hν
  have hwq := hps.outW rfl
  have hok : WriteOk A tid iv c k l tr extra (M.last + 1) := by
    refine ⟨by omega_t, fun a ha => ?_⟩
    cases tr' with
    | none =>
      cases tr with
      | none => cases ha
      | some _ => exact htr.elim
    | some a' =>
      cases tr with
      | none => exact htr.elim
      | some a0 =>
        cases ha
        have ha' : a' ≤ M.last := by
          refine Nat.le_of_not_lt fun hlt => ?_
          have := htrP a' rfl hlt
          have := Nat.le_max_right (writePre A iv' c' k extra') (c'.views.getCoh l)
          omega_t
        have e : a = a' := (show VR M.last a a' from htr).eq' ha'
        subst e
        refine ⟨by omega_t, ?_⟩
        have hat := (hok'.2 a rfl).2
        cases hrd : c.mem.read? l a with
        | none => unfold Memory.atomic; rw [hrd]
        | some val =>
          have hrd0 : c'.mem.read? l a = some val := by rw [hps.memP.read? ha', ← hps.memR.read? ha']; exact hrd
          apply Memory.atomic_of_forall
          intro u y h1 h2 hy hl
          have hum : u ≤ M.last := by omega_t
          rw [hps.memR.get? hum, ← hps.memP.get? hum] at hy
          exact Memory.atomic_elim hat hrd0 u y h1 (by omega_t) hy hl
  have htp : M.last + 1 ∈ c.prom := by
    rw [hps.promEq]; unfold outL; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hmem := (mem_writeSuccs A tid (iv := iv) (c := c) (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr)
    (extra := extra) (xr := xr)).mpr (Or.inl ⟨M.last + 1, htp, w, hwq, hwl, hwv, hwt, hok, rfl⟩)
  have hmem' := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
    (extra := extra') (xr := xr')).mpr (Or.inr ⟨hok', rfl⟩)
  refine ⟨_, hmem, ?_⟩
  have hxw : ({ loc := l, val := v, tid } : Msg) = w := by
    cases w; simp only at hwl hwv hwt; subst hwl hwv hwt; rfl
  have hnot' : c'.mem.last + 1 ∉ c'.prom := fun h => by have := hps.promLe _ h; omega_t
  have hnotm : M.last + 1 ∉ c'.prom := fun h => by have := hps.promLe _ h; omega_t
  have hpe' : (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) = c'.prom := by
    rw [List.erase_append_right _ hnot']; simp
  have hpe : c.prom.erase (M.last + 1) = c'.prom := by
    rw [hps.promEq]; unfold outL; simp only [↓reduceIte]
    rw [List.erase_append_right _ hnotm]; simp
  have hfl : c'.prom.filter (· ≤ M.last) = c'.prom :=
    List.filter_eq_self.mpr fun s h => by simpa using hps.promLe s h
  -- no performed replay write to `l` above `m`: its `coh l` is at most `m`
  have hnoW : ∀ s y, M.last < s → s ≠ M.last + 1 → c.mem.get? s = some y → y.loc ≠ l := by
    intro s y h1 h2 hy hyl
    have := hps.ownR s y h1 (fun _ => h2) hy
    rw [hyl] at this
    have := Nat.le_max_right (writePre A iv c k extra) (c.views.getCoh l)
    omega_t
  have hlastW : IsLast c.mem M.last false l (M.last + 1) :=
    ⟨by omega_t, Pf.of_false, ⟨w, hwq, hwl⟩, fun s' y h1 _ hy => hnoW s' y (by omega_t) (by omega_t) hy⟩
  have hgetq : ∀ s y, c'.mem.get? s = some y → (c'.mem.append { loc := l, val := v, tid }).1.get? s = some y :=
    fun s y h => by rw [Memory.get?_append_of_le _ _ _ (c'.mem.last_le_of_get?_eq_some h)]; exact h
  exact
    { ps :=
        { rel := by
            refine afterWrite_rel A ?_ hiv.addrW _ _ _ _ (VR.of_gt (by omega_t) (by omega_t))
              (hiv.addrR.max (hiv.dataR.max hex)) _ _ hxr ?_ hps.rel.loadViews hps.rel.rmwWrote hps.rel.stores
            · exact hrel
            · show (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) = (c.prom.erase (M.last + 1)).filter _
              rw [hpe', hpe, hfl]
          promEq := by
            show c.prom.erase (M.last + 1) = (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) ++ outL M.last false
            rw [hpe, hpe']; simp [outL]
          promLe := by
            show ∀ s ∈ (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1), _; rw [hpe']; exact hps.promLe
          memR := hps.memR
          memP := hps.memP.trans (Memory.Prefix.append _ _)
          outW := fun h => Bool.noConfusion h
          tidR := hps.tidR
          tidP := fun u y hu hy => by
            rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
            · exact hps.tidP u y hu hy'
            · rfl
          ownR := fun u y hu _ hy => by
            rw [afterWrite_getCoh]
            by_cases e : u = M.last + 1
            · subst e
              have hy' : c.mem.get? (M.last + 1) = some y := hy
              rw [hwq] at hy'; cases hy'
              simp only [hwl, ↓reduceIte]; exact Nat.le_max_right _ _
            · have := hps.ownR u y hu (fun _ => e) hy
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
              exact (hps.fwdR l' f hf hm).unout hwq (by rw [hwl]; exact fun h => e h.symm)
          fwdP := fun l' f hf hm => by
            rw [afterWrite_getFwd] at hf
            by_cases e : l' = l
            · subst e
              simp only [↓reduceIte, Option.some.injEq] at hf
              subst hf
              exact IsLast.append_new _ hML Pf.of_false
            · simp only [e, ↓reduceIte] at hf
              exact (hps.fwdP l' f hf hm).append_ne (fun h => e h.symm)
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
                · obtain ⟨s', h1, h2⟩ := hps.lat.fwd l' s y (hl.toOut hwq (by rw [hwl]; exact e)) hy
                  exact ⟨s', h1.append_ne e, hgetq s' y h2⟩
              back := fun u y hu hy => by
                rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
                · obtain ⟨s, z, h1, -, h3, h4⟩ := hps.lat.back u y hu hy'
                  exact ⟨s, z, h1, Pf.of_false, h3, h4⟩
                · exact ⟨M.last + 1, w, by omega_t, Pf.of_false, hwq, hwl⟩ }
          bnd := (writeSuccs_bnd A tid iv' hps.bnd hiv' hex' hmem').1
          pnow := fun _ => .inr ⟨max (writePre A iv' c' k extra') (c'.views.getCoh l), hν,
            List.mem_append_right _ (by rw [hxw]; exact List.mem_singleton_self _)⟩ }
      ownP := fun u y hu hy => by
        rw [afterWrite_getCoh]
        rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨rfl, rfl⟩
        · have := hs.ownP u y hu hy'
          split
          · rename_i e; rw [e] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
          · exact this
        · simp only [↓reduceIte]; exact Nat.le_max_right _ _
      xclP := fun a ν l1 hx h1 => by
        rw [afterWrite_getCoh]
        have hx1 : (if xcl then none else c'.views.xclb) = some (a, ν, l1) := hx
        split at hx1
        · cases hx1
        · have := hs.xclP a ν l1 hx1 h1
          split
          · rename_i e; rw [e] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
          · exact this
      bndR := (writeSuccs_bnd A tid iv hs.bndR hivR hexR hmem).1
      fresh := fun h => Bool.noConfusion h }

/-- **A fresh write, replayed fresh** (either phase): the original appends at
`|Mp| + 1`, the replay appends the same message at `|Mq| + 1`. Not the
conversion: while `w` is outstanding, the message is not `w` with a
constraining view `≤ m` (`hnc`). -/
theorem write_now_rsim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.RSim M tid w out B c') (hiv : iv.Rel M.last iv') (hivR : iv.Le c.mem.last) (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htrR : ∀ a, tr = some a → a ≤ c.mem.last)
    {extra extra' : View} (hex : VR M.last extra extra') (hexR : extra ≤ c.mem.last) (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr')
    (hok' : WriteOk A tid iv' c' k l tr' extra' (c'.mem.last + 1))
    (hnc : out = true → ({ loc := l, val := v, tid } : Msg) = w →
      M.last < max (writePre A iv' c' k extra') (c'.views.getCoh l)) :
    ∃ c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr,
      c2.RSim M tid w out B
        (afterWrite A iv'
          { c' with mem := (c'.mem.append { loc := l, val := v, tid }).1,
                    prom := c'.prom ++ [c'.mem.last + 1],
                    promisedNow := c'.promisedNow ++
                      [({ loc := l, val := v, tid }, max (writePre A iv' c' k extra') (c'.views.getCoh l))] }
          (A.storeKind k) xcl l v (c'.mem.last + 1) (max iv'.addrR (max iv'.dataR extra')) false xr') := by
  have hps := hs.ps
  have hrel := hps.rel.views
  have hBR := writePre_le A (l := l) hs.bndR hivR k hexR
  have hML := hps.memP.last_le
  have hMR := hps.memR.last_le
  have hok : WriteOk A tid iv c k l tr extra (c.mem.last + 1) := by
    refine ⟨by omega_t, fun a ha => ⟨by have := htrR a ha; omega_t, ?_⟩⟩
    cases tr' with
    | none =>
      cases tr with
      | none => cases ha
      | some _ => exact htr.elim
    | some a' =>
      cases tr with
      | none => exact htr.elim
      | some a0 =>
        cases ha
        exact hs.atomic htr (fun _ => (hok'.2 a' rfl).2) (by omega_t)
  have hmem := (mem_writeSuccs A tid (iv := iv) (c := c) (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr)
    (extra := extra) (xr := xr)).mpr (Or.inr ⟨hok, rfl⟩)
  have hmem' := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
    (extra := extra') (xr := xr')).mpr (Or.inr ⟨hok', rfl⟩)
  refine ⟨_, hmem, ?_⟩
  have ht' : VR M.last (c.mem.last + 1) (c'.mem.last + 1) := VR.of_gt (by omega_t) (by omega_t)
  have hnot' : c'.mem.last + 1 ∉ c'.prom := fun h => by have := hps.promLe _ h; omega_t
  have hnot : c.mem.last + 1 ∉ c.prom := fun h => by have := hps.prom_le_last _ h; omega_t
  have hpe : (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) = c.prom := by
    rw [List.erase_append_right _ hnot]; simp
  have hpe' : (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) = c'.prom := by
    rw [List.erase_append_right _ hnot']; simp
  have hpf := hps.pf_fresh
  exact
    { ps :=
        { rel := by
            refine afterWrite_rel A ?_ hiv.addrW _ _ _ _ ht' (hiv.addrR.max (hiv.dataR.max hex)) _ _ hxr ?_
              hps.rel.loadViews hps.rel.rmwWrote hps.rel.stores
            · exact hrel
            · show (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) =
                ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).filter (· ≤ M.last)
              rw [hpe, hpe']; exact hps.rel.prom
          promEq := by
            show (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) =
              (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) ++ outL M.last out
            rw [hpe, hpe']; exact hps.promEq
          promLe := by
            show ∀ s ∈ (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1), _; rw [hpe']; exact hps.promLe
          memR := hps.memR.trans (Memory.Prefix.append _ _)
          memP := hps.memP.trans (Memory.Prefix.append _ _)
          outW := fun ho => by
            show (c.mem.append _).1.get? _ = _
            rw [Memory.get?_append_of_le _ _ _ (c.mem.last_le_of_get?_eq_some (hps.outW ho))]; exact hps.outW ho
          tidR := fun u y hu hy => by
            rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
            · exact hps.tidR u y hu hy'
            · rfl
          tidP := fun u y hu hy => by
            rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
            · exact hps.tidP u y hu hy'
            · rfl
          ownR := fun u y hu hpf' hy => by
            rw [afterWrite_getCoh]
            rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨rfl, rfl⟩
            · have := hps.ownR u y hu hpf' hy'
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
              exact (hps.fwdR l' f hf hm).append_ne (fun h => e h.symm)
          fwdP := fun l' f hf hm => by
            rw [afterWrite_getFwd] at hf
            by_cases e : l' = l
            · subst e
              simp only [↓reduceIte, Option.some.injEq] at hf
              subst hf
              exact IsLast.append_new _ hML Pf.of_false
            · simp only [e, ↓reduceIte] at hf
              exact (hps.fwdP l' f hf hm).append_ne (fun h => e h.symm)
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
                  obtain ⟨s', h1, h2⟩ := hps.lat.fwd l' s y hl0 hy0
                  exact ⟨s', h1.append_ne e, by
                    show (c'.mem.append _).1.get? s' = _
                    rw [Memory.get?_append_of_le _ _ _ (c'.mem.last_le_of_get?_eq_some h2)]; exact h2⟩
              back := fun u y hu hy => by
                rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
                · obtain ⟨s, z, h1, h2, h3, h4⟩ := hps.lat.back u y hu hy'
                  exact ⟨s, z, h1, h2, by
                    show (c.mem.append _).1.get? s = _
                    rw [Memory.get?_append_of_le _ _ _ (c.mem.last_le_of_get?_eq_some h3)]; exact h3, h4⟩
                · exact ⟨c.mem.last + 1, _, by omega_t, hpf, Memory.get?_append_last _ _, rfl⟩ }
          bnd := (writeSuccs_bnd A tid iv' hps.bnd hiv' hex' hmem').1
          pnow := fun ho => (hps.pnow ho).imp id (fun ⟨ν, h1, h2⟩ => ⟨ν, h1, List.mem_append_left _ h2⟩) }
      ownP := fun u y hu hy => by
        rw [afterWrite_getCoh]
        rcases Memory.get?_append_eq_some _ _ hy with ⟨-, hy'⟩ | ⟨rfl, rfl⟩
        · have := hs.ownP u y hu hy'
          split
          · rename_i e; rw [e] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
          · exact this
        · simp only [↓reduceIte]; exact Nat.le_max_right _ _
      xclP := fun a ν l1 hx h1 => by
        rw [afterWrite_getCoh]
        have hx1 : (if xcl then none else c'.views.xclb) = some (a, ν, l1) := hx
        split at hx1
        · cases hx1
        · have := hs.xclP a ν l1 hx1 h1
          split
          · rename_i e; rw [e] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
          · exact this
      bndR := (writeSuccs_bnd A tid iv hs.bndR hivR hexR hmem).1
      fresh := fun ho ν hν h => by
        rcases List.mem_append.mp h with h | h
        · exact hs.fresh ho ν hν h
        · rw [List.mem_singleton, Prod.mk.injEq] at h
          have := hnc ho h.1.symm
          omega_t }

/-- **A fulfilment, replayed by the same fulfilment** (either phase; the
original's promises are all at most `m`). -/
theorem write_ful_rsim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.RSim M tid w out B c') (hiv : iv.Rel M.last iv') (hivR : iv.Le c.mem.last) (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr')
    {extra extra' : View} (hex : VR M.last extra extra') (hexR : extra ≤ c.mem.last) (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr')
    {t : Time} (htp' : t ∈ c'.prom) {y : Msg} (hy' : c'.mem.get? t = some y) (hyl : y.loc = l) (hyv : y.val = v)
    (hyt : y.tid = tid) (hok' : WriteOk A tid iv' c' k l tr' extra' t) :
    ∃ c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr,
      c2.RSim M tid w out B (afterWrite A iv' c' (A.storeKind k) xcl l v t (max iv'.addrR (max iv'.dataR extra')) true xr') := by
  have hps := hs.ps
  have hrel := hps.rel.views
  have htm : t ≤ M.last := hps.promLe t htp'
  have hB := (writePre_vr A hrel hiv k hex).max (hrel.coh l)
  have hbt : max (writePre A iv' c' k extra') (c'.views.getCoh l) ≤ M.last := by have := hok'.1; omega_t
  have hok : WriteOk A tid iv c k l tr extra t := by
    refine ⟨by rw [hB.eq' hbt]; exact hok'.1, fun a ha => ?_⟩
    cases tr' with
    | none =>
      cases tr with
      | none => cases ha
      | some _ => exact htr.elim
    | some a' =>
      cases tr with
      | none => exact htr.elim
      | some a0 =>
        cases ha
        have hr := hok'.2 a' rfl
        have hra : a = a' := (show VR M.last a a' from htr).eq' (by omega_t)
        subst hra
        refine ⟨hr.1, ?_⟩
        rw [hps.memR.atomic_eq hr.1 htm, ← hps.memP.atomic_eq hr.1 htm]; exact hr.2
  have htp : t ∈ c.prom := by rw [hps.promEq]; exact List.mem_append_left _ htp'
  have hy : c.mem.get? t = some y := by rw [hps.memR.get? htm, ← hps.memP.get? htm]; exact hy'
  have hmem := (mem_writeSuccs A tid (iv := iv) (c := c) (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr)
    (extra := extra) (xr := xr)).mpr (Or.inl ⟨t, htp, y, hy, hyl, hyv, hyt, hok, rfl⟩)
  have hmem' := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
    (extra := extra') (xr := xr')).mpr (Or.inl ⟨t, htp', y, hy', hyl, hyv, hyt, hok', rfl⟩)
  refine ⟨_, hmem, ?_⟩
  exact
    { ps :=
        { rel := afterWrite_rel A hrel hiv.addrW _ _ _ _ (VR.refl _ _) (hiv.addrR.max (hiv.dataR.max hex))
            true true hxr (by rw [hps.rel.prom, List.erase_filter]) hps.rel.loadViews hps.rel.rmwWrote hps.rel.stores
          promEq := by
            show c.prom.erase t = c'.prom.erase t ++ outL M.last out
            rw [hps.promEq, List.erase_append_left _ htp']
          promLe := fun s h => hps.promLe s (List.mem_of_mem_erase h)
          memR := hps.memR
          memP := hps.memP
          outW := hps.outW
          tidR := hps.tidR
          tidP := hps.tidP
          ownR := fun u z h1 h2 hz => Nat.le_trans (hps.ownR u z h1 h2 hz) (Views.getCoh_le_setCoh _ _ _ _)
          fwdR := fun l' f hf hm => by
            rw [afterWrite_getFwd] at hf
            by_cases e : l' = l
            · subst e
              simp only [↓reduceIte, Option.some.injEq] at hf
              subst hf; simp only at hm; omega_t
            · simp only [e, ↓reduceIte] at hf
              exact hps.fwdR l' f hf hm
          fwdP := fun l' f hf hm => by
            rw [afterWrite_getFwd] at hf
            by_cases e : l' = l
            · subst e
              simp only [↓reduceIte, Option.some.injEq] at hf
              subst hf; simp only at hm; omega_t
            · simp only [e, ↓reduceIte] at hf
              exact hps.fwdP l' f hf hm
          lat := hps.lat
          bnd := (writeSuccs_bnd A tid iv' hps.bnd hiv' hex' hmem').1
          pnow := hps.pnow }
      ownP := fun u z h1 hz => Nat.le_trans (hs.ownP u z h1 hz) (Views.getCoh_le_setCoh _ _ _ _)
      xclP := fun a ν l1 hx h1 => by
        have hx1 : (if xcl then none else c'.views.xclb) = some (a, ν, l1) := hx
        split at hx1
        · cases hx1
        · exact Nat.le_trans (hs.xclP a ν l1 hx1 h1) (Views.getCoh_le_setCoh _ _ _ _)
      bndR := (writeSuccs_bnd A tid iv hs.bndR hivR hexR hmem).1
      fresh := hs.fresh }

/-- **One write, replayed backwards**: a fulfilment by the same fulfilment;
while `w` is outstanding, the fresh write of `w` with constraining view
`≤ m` by the fulfilment of `m + 1` (phase A ends); any other fresh write by a
fresh write. -/
theorem writeSuccs_rsim {M : Memory} {w : Msg} {out : Bool} {B : Prop} {iv iv' : InstrViews} {c c' : Ctx}
    (hs : c.RSim M tid w out B c') (hiv : iv.Rel M.last iv') (hivR : iv.Le c.mem.last) (hiv' : iv'.Le c'.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htrR : ∀ a, tr = some a → a ≤ c.mem.last)
    (htrP : ∀ a, tr' = some a → M.last < a → a ≤ c'.views.getCoh l)
    {extra extra' : View} (hex : VR M.last extra extra') (hexR : extra ≤ c.mem.last) (hex' : extra' ≤ c'.mem.last)
    {xr xr' : View} (hxr : VR M.last xr xr')
    {c2' : Ctx} (h : c2' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr') :
    ∃ c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr, ∃ out2, c2.RSim M tid w out2 B c2' ∧
      (out = false → out2 = false) := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, htp, y, hy, hyl, hyv, hyt, hok, rfl⟩ | ⟨hok, rfl⟩
  · obtain ⟨c2, h1, h2⟩ := write_ful_rsim A tid hs hiv hivR hiv' htr hex hexR hex' hxr htp hy hyl hyv hyt hok
    exact ⟨c2, h1, out, h2, id⟩
  · by_cases hconv : out = true ∧ ({ loc := l, val := v, tid } : Msg) = w ∧
        max (writePre A iv' c' k extra') (c'.views.getCoh l) ≤ M.last
    · obtain ⟨rfl, hw, hν⟩ := hconv
      subst hw
      obtain ⟨c2, h1, h2⟩ := write_conv_rsim A tid hs hiv hivR hiv' htr htrP hex hexR hex' hxr rfl rfl rfl hok hν
      exact ⟨c2, h1, false, h2, fun _ => rfl⟩
    · have hnc : out = true → ({ loc := l, val := v, tid } : Msg) = w →
          M.last < max (writePre A iv' c' k extra') (c'.views.getCoh l) := fun ho hw =>
        Nat.lt_of_not_le fun hle => hconv ⟨ho, hw, hle⟩
      obtain ⟨c2, h1, h2⟩ := write_now_rsim A tid (xcl := xcl) hs hiv hivR hiv' htr htrR hex hexR hex' hxr hok hnc
      exact ⟨c2, h1, out, h2, id⟩

end Rules

/-! ## Memory-silent steps -/

/-- A step that keeps coherence, forwarding, memory, promises, load views and
the original's promised writes on both sides, and does not create a pending
exclusive, keeps the replay relation. -/
theorem _root_.Kraken.Promising.Ctx.RSim.congr {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {B : Prop}
    {c c' c2 c2' : Ctx} (hs : c.RSim M tid w out B c')
    (hv : c2.views.Rel M.last c2'.views) (hcoh : ∀ l, c2.views.getCoh l = c.views.getCoh l)
    (hcoh' : ∀ l, c2'.views.getCoh l = c'.views.getCoh l)
    (hf : ∀ l, c2.views.getFwd l = c.views.getFwd l) (hf' : ∀ l, c2'.views.getFwd l = c'.views.getFwd l)
    (hm : c2.mem = c.mem) (hm' : c2'.mem = c'.mem) (hp : c2.prom = c.prom) (hp' : c2'.prom = c'.prom)
    (hlv : c2.loadViews = c.loadViews) (hlv' : c2'.loadViews = c'.loadViews)
    (hsv : VR M.last c2.succView c2'.succView) (hrw : c2.rmwWrote = c2'.rmwWrote) (hst : c2.stores = c2'.stores)
    (hb : c2'.Bnd) (hpn : c2'.promisedNow = c'.promisedNow)
    (hx' : ∀ a ν l, c2'.views.xclb = some (a, ν, l) → c'.views.xclb = some (a, ν, l)) (hbR : c2.Bnd) :
    c2.RSim M tid w out B c2' :=
  { ps := hs.ps.congr hv hcoh hf hf' hm hm' hp hp' hlv hlv' hsv hrw hst hb hpn
    ownP := by rw [hm']; intro u x h1 hx; rw [hcoh']; exact hs.ownP u x h1 hx
    xclP := fun a ν l h1 h2 => by rw [hcoh']; exact hs.xclP a ν l (hx' a ν l h1) h2
    bndR := hbR
    fresh := by rw [hpn]; exact hs.fresh }

section Silent

variable {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {B : Prop} {c c' : Ctx}

theorem fenceStep_rsim (hs : c.RSim M tid w out B c') (k : FenceKind) :
    (fenceStep c k).RSim M tid w out B (fenceStep c' k) := by
  have hp := fenceStep_psim hs.ps k
  have hb := fenceStep_bnd hs.bndR k
  exact
    { ps := hp
      ownP := by
        rw [fenceStep_mem]; intro u x h1 hx
        cases k <;> exact hs.ownP u x h1 hx
      xclP := by intro a ν l h1 h2; cases k <;> exact hs.xclP a ν l h1 h2
      bndR := hb
      fresh := by rw [fenceStep_promisedNow]; exact hs.fresh }

theorem fenceOpt_rsim (hs : c.RSim M tid w out B c') (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).RSim M tid w out B (if b then fenceStep c' k else c') := by
  cases b
  · exact hs
  · exact fenceStep_rsim hs k

theorem rmwPost_rsim (A : Arch) (hs : c.RSim M tid w out B c') (k : RmwKind) (noRet : Bool) (l : Loc) :
    (rmwPost A k noRet l c).RSim M tid w out B (rmwPost A k noRet l c') := by
  have hp := rmwPost_psim A hs.ps k noRet l
  have hb := (rmwPost_bnd A hs.bndR k noRet l).1
  refine { ps := hp, ownP := ?_, xclP := ?_, bndR := hb, fresh := ?_ }
  · rw [rmwPost_mem]; intro u x h1 hx
    have := hs.ownP u x h1 hx
    unfold rmwPost; split <;> exact this
  · intro a ν l1 h1 h2
    have h1' : c'.views.xclb = some (a, ν, l1) := by
      revert h1; unfold rmwPost; split <;> exact id
    have := hs.xclP a ν l1 h1' h2
    unfold rmwPost; split <;> exact this
  · have : (rmwPost A k noRet l c').promisedNow = c'.promisedNow := by unfold rmwPost; split <;> rfl
    rw [this]; exact hs.fresh

theorem xclFail_rsim (hs : c.RSim M tid w out B c') (l : Loc) :
    Ctx.RSim M tid w out B
      { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
      { c' with views := { c'.views with xclb := none }, succView := 0, log := c'.log ++ [.xclFail l] } :=
  hs.congr hs.ps.rel.views.xclbNone (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl
    rfl rfl (VR.refl _ _) hs.ps.rel.rmwWrote hs.ps.rel.stores
    ⟨hs.ps.bnd.views.xclbNone, hs.ps.bnd.loadViews, Nat.zero_le _⟩ rfl (fun _ _ _ h => by cases h)
    ⟨hs.bndR.views.xclbNone, hs.bndR.loadViews, Nat.zero_le _⟩

end Silent

/-! ## The future of the original run -/

/-- Every "promise now" write recorded from `c` to `c2` has a constraining
view at least `c`'s `coh` of its location. -/
def PnBound (c c2 : Ctx) : Prop :=
  ∀ p ∈ c2.promisedNow, p ∉ c.promisedNow → c.views.getCoh p.1.loc ≤ p.2

/-- `PnBound` together with `Ctx.DOrd` (so that it composes). -/
def PnD (c c2 : Ctx) : Prop := PnBound c c2 ∧ c.DOrd c2

theorem PnD.trans {a b c : Ctx} (h₁ : PnD a b) (h₂ : PnD b c) : PnD a c := by
  refine ⟨fun p hp hn => ?_, h₁.2.trans h₂.2⟩
  by_cases hb : p ∈ b.promisedNow
  · exact h₁.1 p hb hn
  · exact Nat.le_trans (h₁.2.coh _) (h₂.1 p hp hb)

theorem PnD.of_eq {a b : Ctx} (hp : b.promisedNow = a.promisedNow) (hd : a.DOrd b) : PnD a b :=
  ⟨fun _ h hn => absurd (hp ▸ h) hn, hd⟩

theorem PnD.refl (c : Ctx) : PnD c c := .of_eq rfl (.refl c)

/-- **The original's `coh w.loc` is at most `m` at `cm`**, if `w` has not yet
been written with a constraining view `≤ m` and the instruction ends with
`FutOk`. -/
def FutOk (M : Memory) (w : Msg) (c : Ctx) : Prop :=
  c.views.getCoh w.loc ≤ M.last ∨ ∃ ν, ν ≤ M.last ∧ (w, ν) ∈ c.promisedNow

theorem fut_back {M : Memory} {w : Msg} {cm c2 : Ctx} (h : PnD cm c2)
    (hfr : ∀ ν, ν ≤ M.last → (w, ν) ∉ cm.promisedNow) (hF : FutOk M w c2) : cm.views.getCoh w.loc ≤ M.last := by
  rcases hF with hF | ⟨ν, hν, hm⟩
  · exact Nat.le_trans (h.2.coh _) hF
  · exact Nat.le_trans (h.1 _ hm (hfr ν hν)) hν

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem writeSuccs_pnD {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c2 : Ctx} (h : c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : PnD c c2 := by
  refine ⟨?_, writeSuccs_dord A tid iv h⟩
  rcases (mem_writeSuccs A tid).mp h with ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩
  · intro p hp hn; exact absurd hp hn
  · intro p hp hn
    change p ∈ c.promisedNow ++ _ at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact absurd hp hn
    · rw [List.mem_singleton] at hp; subst hp; exact Nat.le_max_right _ _

theorem fenceOpt_pnD (c : Ctx) (b : Bool) (k : FenceKind) : PnD c (if b then fenceStep c k else c) := by
  cases b
  · exact .refl c
  · exact .of_eq (fenceStep_promisedNow c k) (.fenceStep c k)

theorem rmwPost_pnD (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : PnD c (rmwPost A k noRet l c) :=
  .of_eq (by unfold rmwPost; split <;> rfl) (Ctx.DOrd.rmwPost A c k noRet l)

theorem runTree_pnD {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → PnD c c' := by
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact .refl _
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i c s c' h
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact (PnD.of_eq (readSuccs_mp A iv hx).2 (readSuccs_dord A iv hx)).trans (ih x.2.1 x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_pnD A tid _ hc0).trans (ih true c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      have h0 : PnD c { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq rfl (.of_eq (Nat.le_refl _) (fun _ => Nat.le_refl _) rfl rfl)
      exact h0.trans (ih false _ s c' h.2)
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (PnD.of_eq (fenceStep_promisedNow c k) (Ctx.DOrd.fenceStep c k)).trans (ih () _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := fenceOpt_pnD c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (PnD.of_eq (readSuccs_mp A iv h2).2 (readSuccs_dord A iv h2))
    simp only at h
    split at h
    · exact (h12.trans (fenceOpt_pnD c2 A.rmwFence .sy)).trans (ih old _ s c' h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      refine ((h12.trans (writeSuccs_pnD A tid _ hc3)).trans ?_).trans (ih old _ s c' h)
      exact (rmwPost_pnD A c3 k noRet l).trans (fenceOpt_pnD _ A.rmwFence .sy)

end Rules

/-! ## One instruction's event tree -/

section Rules

variable (A : Arch) (tid : Nat)

private theorem getLastD_le' {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) :
    ∀ d, d ≤ n → xs.getLastD d ≤ n := by
  induction xs with
  | nil => intro d hd; exact hd
  | cons x xs ih =>
    intro _ _
    rw [List.getLastD_cons]
    exact ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν)) x (h x List.mem_cons_self)

private theorem out_of {out out1 : Bool} (ho : out = false → out1 = false) (h1 : out1 = true) : out = true := by
  cases out
  · rw [ho rfl] at h1; cases h1
  · rfl

/-- **One instruction's event tree, replayed backwards.** A run of the event
tree from the original context is matched by a run from the replay context,
ending in related contexts; phase A may end inside the tree (at the
original's fresh write of `w`), never restart. `hF`: while `w` is outstanding,
the instruction ends with `FutOk`. -/
theorem runTree_rsim {σ : Type} {M : Memory} {w : Msg} {B : Prop} {iv iv' : InstrViews} (hiv : iv.Rel M.last iv')
    (tree : EvTree σ) :
    ∀ (out : Bool) (c c' : Ctx) (s : σ) (c2' : Ctx), c.RSim M tid w out B c' → iv.Le c.mem.last →
      iv'.Le c'.mem.last → .ok (s, c2') ∈ runTree A tid iv' c' tree → (out = true → FutOk M w c2') →
      ∃ c2 out2, .ok (s, c2) ∈ runTree A tid iv c tree ∧ c2.RSim M tid w out2 B c2' ∧
        (out = false → out2 = false) := by
  induction tree with
  | done s0 =>
    intro out c c' s c2' hs _ _ h _
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c, out, by simp [runTree], hs, id⟩
  | fault msg =>
    intro out c c' s c2' _ _ _ h _
    simp [runTree] at h
  | choose n k ih =>
    intro out c c' s c2' hs hivR hiv' h hF
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨c2, out2, h', hs', ho⟩ := ih i out c c' s c2' hs hivR hiv' h hF
    exact ⟨c2, out2, ⟨i, hi, h'⟩, hs', ho⟩
  | load k xcl l ret ih =>
    intro out c c' s c2' hs hivR hiv' h hF
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t', v', c0'⟩, hx', h⟩ := h
    have hfut : out = true → w.loc = l → c0'.views.getCoh l ≤ M.last := by
      intro ho hl
      have := fut_back (runTree_pnD A tid iv' _ c0' s c2' h)
        (fun ν hν hm => hs.fresh ho ν hν (by rw [← (readSuccs_mp A iv' hx').2]; exact hm)) (hF ho)
      rw [hl] at this; exact this
    obtain ⟨⟨t, v, c0⟩, hx, hv, -, -, -, hsim⟩ := readSuccs_rsim A tid hs hiv hivR hiv' hx' hfut
    simp only at hv
    have hm0 : c0.mem = c.mem := (readSuccs_mp A iv hx).1
    have hm0' : c0'.mem = c'.mem := (readSuccs_mp A iv' hx').1
    obtain ⟨c2, out2, h', hs', ho⟩ := ih v' out c0 c0' s c2' hsim (hm0 ▸ hivR) (hm0' ▸ hiv') h hF
    exact ⟨c2, out2, ⟨(t, v, c0), hx, by rw [hv]; exact h'⟩, hs', ho⟩
  | store k xcl l v ret ih =>
    intro out c c' s c2' hs hivR hiv' h hF
    have hv := hs.ps.rel.views
    have htr : OptR M.last (if xcl then c.views.xclb.map (·.1) else none)
        (if xcl then c'.views.xclb.map (·.1) else none) := by
      cases xcl
      · trivial
      · have hx := hv.xclb
        revert hx
        rcases c.views.xclb with _ | ⟨a, b, l1⟩ <;> rcases c'.views.xclb with _ | ⟨a', b', l2⟩ <;>
          simp only [XclbR, OptR, Option.map, imp_self, ↓reduceIte]
        rintro ⟨h1, -, -⟩; exact h1
    have htrR : ∀ a, (if xcl then c.views.xclb.map (·.1) else none) = some a → a ≤ c.mem.last := by
      intro a ha
      cases xcl
      · cases ha
      · simp only [↓reduceIte] at ha
        cases hx : c.views.xclb with
        | none => rw [hx] at ha; cases ha
        | some p =>
          rw [hx] at ha
          obtain ⟨a0, b0, l0⟩ := p
          simp only [Option.map_some, Option.some.injEq] at ha
          subst ha
          exact (hs.bndR.views.xclb _ _ _ hx).1
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨hp, c0', hc0', h⟩ := h
      have htrP : ∀ a, (if xcl then c'.views.xclb.map (·.1) else none) = some a → M.last < a →
          a ≤ c'.views.getCoh l := by
        intro a ha hm
        cases xcl
        · cases ha
        · simp only [↓reduceIte] at ha
          cases hx : c'.views.xclb with
          | none => rw [hx] at ha; cases ha
          | some p =>
            obtain ⟨a0, b0, l0⟩ := p
            rw [hx] at ha hp
            simp only [Option.map_some, Option.some.injEq] at ha
            subst ha
            have hl0 : l0 = l := by simpa using hp
            subst hl0
            exact hs.xclP _ _ _ hx hm
      have hivs : (iv.forStore c.stores).Rel M.last (iv'.forStore c'.stores) :=
        hs.ps.rel.stores ▸ hiv.forStore c.stores
      obtain ⟨c0, hc0, out1, hsim, ho1⟩ := writeSuccs_rsim A tid hs hivs (hivR.forStore c.stores)
        (hiv'.forStore c'.stores) htr htrR htrP (VR.refl _ 0) (Nat.zero_le _) (Nat.zero_le _)
        (xr := if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0)
        (xr' := if xcl then (c'.views.xclb.map (·.2.1)).getD 0 else 0)
        (VR.ite hs.ps.rel.views.xclb.xclRead (VR.refl _ _)) hc0'
      have hl := (writeSuccs_bnd A tid _ hs.bndR (hivR.forStore c.stores) (Nat.zero_le _) hc0).2
      have hl' := (writeSuccs_bnd A tid _ hs.ps.bnd (hiv'.forStore c'.stores) (Nat.zero_le _) hc0').2
      obtain ⟨c2, out2, h', hs', ho2⟩ := ih true out1 c0 c0' s c2' hsim (hivR.mono hl) (hiv'.mono hl') h
        (fun h1 => hF (out_of ho1 h1))
      refine ⟨c2, out2, Or.inl ?_, hs', fun e => ho2 (ho1 e)⟩
      rw [List.mem_ite_nil_left, List.mem_flatMap]
      refine ⟨?_, c0, hc0, h'⟩
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
      obtain ⟨c2, out2, h', hs', ho⟩ := ih false out _ _ s c2' (xclFail_rsim hs l) hivR hiv' h.2 hF
      refine ⟨c2, out2, Or.inr ?_, hs', ho⟩
      rw [List.mem_ite_nil_right]
      exact ⟨h.1, h'⟩
  | fence k ret ih =>
    intro out c c' s c2' hs hivR hiv' h hF
    simp only [runTree] at h ⊢
    exact ih () out _ _ s c2' (fenceStep_rsim hs k) (by rw [fenceStep_mem]; exact hivR)
      (by rw [fenceStep_mem]; exact hiv') h hF
  | rmw k noRet l op ret ih =>
    intro out c c' s c2' hs hivR hiv' h hF
    simp only [runTree] at h ⊢
    have hs1 := fenceOpt_rsim hs A.rmwFence .sy
    have hm1 : (if A.rmwFence then fenceStep c .sy else c).mem = c.mem := by
      split <;> simp only [fenceStep_mem]
    have hm1' : (if A.rmwFence then fenceStep c' .sy else c').mem = c'.mem := by
      split <;> simp only [fenceStep_mem]
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at hs1 hm1 ⊢
    generalize (if A.rmwFence then fenceStep c' .sy else c') = c1' at h hs1 hm1'
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr', old', c3'⟩, hx', h⟩ := h
    simp only at h
    have hm3' : c3'.mem = c1'.mem := (readSuccs_mp A iv' hx').1
    have hpn3' : c3'.promisedNow = c1'.promisedNow := (readSuccs_mp A iv' hx').2
    -- the rest of the original instruction after its read
    have hrest : PnD c3' c2' := by
      split at h
      · exact (fenceOpt_pnD c3' _ _).trans (runTree_pnD A tid iv' _ _ s c2' h)
      · rw [List.mem_flatMap] at h
        obtain ⟨c4', hc4', h⟩ := h
        change .ok (s, c2') ∈ runTree A tid iv'
          (if A.rmwFence then fenceStep (rmwPost A k noRet l c4') .sy else rmwPost A k noRet l c4') (ret old') at h
        exact ((writeSuccs_pnD A tid _ hc4').trans ((rmwPost_pnD A c4' k noRet l).trans (fenceOpt_pnD _ _ _))).trans
          (runTree_pnD A tid iv' _ _ s c2' h)
    have hfut : out = true → w.loc = l → c3'.views.getCoh l ≤ M.last := by
      intro ho hl
      have := fut_back hrest (fun ν hν hm => hs1.fresh ho ν hν (by rw [← hpn3']; exact hm)) (hF ho)
      rw [hl] at this; exact this
    obtain ⟨⟨tr, old, c3⟩, hx, hv, htr, htrl, htrP, hsim⟩ :=
      readSuccs_rsim A tid hs1 hiv (hm1 ▸ hivR) (hm1' ▸ hiv') hx' hfut
    simp only at hv htr htrl htrP
    have hm3 : c3.mem = c1.mem := (readSuccs_mp A iv hx).1
    split at h
    · rename_i hop
      obtain ⟨c2, out2, h', hs', ho⟩ := ih old' out _ _ s c2' (fenceOpt_rsim hsim A.rmwFence .sy)
        (by split <;> simp only [fenceStep_mem, hm3, hm1] <;> exact hivR)
        (by split <;> simp only [fenceStep_mem, hm3', hm1'] <;> exact hiv') h hF
      refine ⟨c2, out2, List.mem_flatMap.mpr ⟨(tr, old, c3), hx, ?_⟩, hs', ho⟩
      simp only [hv, hop]
      exact h'
    · rename_i new hop
      rw [List.mem_flatMap] at h
      obtain ⟨c4', hc4', h⟩ := h
      change .ok (s, c2') ∈ runTree A tid iv'
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c4') .sy else rmwPost A k noRet l c4') (ret old') at h
      have hiv3 : iv.Le c3.mem.last := by rw [hm3, hm1]; exact hivR
      have hiv3' : iv'.Le c3'.mem.last := by rw [hm3', hm1']; exact hiv'
      have hgl := getLastD_le' hsim.bndR.loadViews 0 (Nat.zero_le _)
      have hgl' := getLastD_le' hsim.ps.bnd.loadViews 0 (Nat.zero_le _)
      obtain ⟨c4, hc4, out1, hsim4, ho1⟩ := writeSuccs_rsim A tid hsim hiv hiv3 hiv3' (tr := some tr)
        (tr' := some tr') htr (fun a ha => by cases ha; rw [hm3]; exact htrl) (fun a ha hm => by cases ha; exact htrP hm)
        (clampL_getLastD hsim.ps.rel.loadViews) hgl hgl' (VR.refl _ 0) hc4'
      have hl := (writeSuccs_bnd A tid iv hsim.bndR hiv3 hgl hc4).2
      have hl' := (writeSuccs_bnd A tid iv' hsim.ps.bnd hiv3' hgl' hc4').2
      have hm5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c4) .sy else rmwPost A k noRet l c4).mem =
          c4.mem := by
        split <;> simp only [fenceStep_mem, rmwPost_mem]
      have hm5' : (if A.rmwFence then fenceStep (rmwPost A k noRet l c4') .sy else rmwPost A k noRet l c4').mem =
          c4'.mem := by
        split <;> simp only [fenceStep_mem, rmwPost_mem]
      obtain ⟨c2, out2, h', hs', ho2⟩ := ih old' out1 _ _ s c2'
        (fenceOpt_rsim (rmwPost_rsim A hsim4 k noRet l) A.rmwFence .sy) (by rw [hm5]; exact hiv3.mono hl)
        (by rw [hm5']; exact hiv3'.mono hl') h (fun h1 => hF (out_of ho1 h1))
      refine ⟨c2, out2, List.mem_flatMap.mpr ⟨(tr, old, c3), hx, ?_⟩, hs', fun e => ho2 (ho1 e)⟩
      simp only [hv, hop, List.mem_flatMap]
      exact ⟨c4, hc4, h'⟩

end Rules

/-! ## Threads -/

section Threads

theorem FwdR.symm {m : Nat} : ∀ {a b : Option FwdItem}, FwdR m a b → FwdR m b a
  | none, none, _ => trivial
  | some _, some _, h => ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
  | none, some _, h => (h : False).elim
  | some _, none, h => (h : False).elim

theorem XclbR.symm {m : Nat} : ∀ {a b : Option (Time × View × Loc)}, XclbR m a b → XclbR m b a
  | none, none, _ => trivial
  | some (_, _, _), some (_, _, _), h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  | none, some _, h => (h : False).elim
  | some _, none, h => (h : False).elim

theorem _root_.Kraken.Promising.Views.Rel.symm {m : Nat} {a b : Views} (h : a.Rel m b) : b.Rel m a :=
  ⟨fun l => (h.coh l).symm, h.vrNew.symm, h.vrOld.symm, h.vrOldNR.symm, h.vwNew.symm, h.vwOld.symm,
    h.vwOldNT.symm, h.vCAP.symm, h.vRel.symm, fun l => FwdR.symm (h.fwd l), XclbR.symm h.xclb⟩

theorem _root_.Kraken.Promising.InstrViews.Rel.symm {m : Nat} {a b : InstrViews} (h : a.Rel m b) : b.Rel m a :=
  ⟨h.addrR.symm, h.addrW.symm, h.dataR.symm, h.dataW.symm, h.condW.symm, h.dataPer.symm⟩

/-- Set a thread's promise set. -/
private def setP (p : List Time) (th : Thread I) : Thread I := { th with prom := p }

private theorem foldl_setP {α : Type} (p : List Time) (f : Thread I → α → Thread I)
    (hf : ∀ t a, f (setP p t) a = setP p (f t a)) :
    ∀ (l : List α) (t : Thread I), l.foldl f (setP p t) = setP p (l.foldl f t)
  | [], _ => rfl
  | a :: l, t => by simp only [List.foldl_cons]; rw [hf]; exact foldl_setP p f hf l _

private def fiBranch (d : InstrDeps I.RegId) (iv : InstrViews) (t : Thread I) : Thread I :=
  if d.isBranch then { t with views := { t.views with vCAP := max t.views.vCAP iv.condW } } else t

private def fiLoads (d : InstrDeps I.RegId) (c : Ctx) (t : Thread I) : Thread I :=
  if d.loadDefs.length == c.loadViews.length then
    (d.loadDefs.zip c.loadViews).foldl (fun t (r, v) => t.setRegView r v v) t
  else
    let v := c.loadViews.foldl max 0
    d.loadDefs.foldl (fun t r => t.setRegView r v v) t

/-- `finishInstr` after its first `let`, on the thread `t0`. -/
private def fiCore (d : InstrDeps I.RegId) (iv : InstrViews) (c : Ctx) (t0 : Thread I) : List (Thread I) :=
  let inR := max iv.addrR iv.dataR
  let inW := max (max iv.addrW iv.dataW) iv.condW
  let inR := if d.isPick then inR else max inR iv.condW
  let t := d.defs.foldl (fun t r => t.setRegView r inR inW) t0
  let t := d.statusDefs.foldl (fun t r => t.setRegView r c.succView c.succView) t
  if d.casLike && c.rmwWrote then
    let readView := c.loadViews.foldl max 0
    let fromRs := d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) readView)) t
    [fiBranch d iv fromRs, fiBranch d iv (fiLoads d c t)]
  else
    [fiBranch d iv (fiLoads d c t)]

private theorem fiBranch_setP (d : InstrDeps I.RegId) (iv : InstrViews) (t : Thread I) (p : List Time) :
    fiBranch d iv (setP p t) = setP p (fiBranch d iv t) := by
  unfold fiBranch; split <;> rfl

private theorem fiLoads_setP (d : InstrDeps I.RegId) (c : Ctx) (t : Thread I) (p : List Time) :
    fiLoads d c (setP p t) = setP p (fiLoads d c t) := by
  unfold fiLoads; split
  · exact foldl_setP p _ (fun _ _ => rfl) _ _
  · exact foldl_setP p _ (fun _ _ => rfl) _ _

private theorem fiCore_setP (d : InstrDeps I.RegId) (iv : InstrViews) (c : Ctx) (t0 : Thread I) (p : List Time) :
    fiCore d iv c (setP p t0) = (fiCore d iv c t0).map (setP p) := by
  unfold fiCore
  simp only
  rw [foldl_setP p _ (fun _ _ => rfl), foldl_setP p _ (fun _ _ => rfl)]
  split
  · rw [foldl_setP p _ (fun _ _ => rfl), fiBranch_setP, fiLoads_setP, fiBranch_setP]; rfl
  · rw [fiLoads_setP, fiBranch_setP]; rfl

/-- `finishInstr` takes its promises from the context. -/
theorem finishInstr_withProm (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (st : I.State) (c : Ctx)
    (p : List Time) :
    finishInstr t d iv st { c with prom := p } =
      (finishInstr t d iv st c).map (fun th => { th with prom := p }) :=
  fiCore_setP d iv c { t with st, views := c.views, prom := c.prom } p

/-- **`finishInstr` on related threads, backwards**: an outcome from the
second thread and context is matched by one from the first (`finishInstr_rel`
with the roles swapped; the promises are taken from the context). -/
theorem finishInstr_rel_back {m : Nat} {t t' : Thread I} {d : InstrDeps I.RegId} {iv iv' : InstrViews}
    {st : I.State} {c c' : Ctx} (h : t.Rel m t') (hc : c.Rel m c') (hiv : iv.Rel m iv') :
    ∀ th' ∈ finishInstr t' d iv' st c', ∃ th ∈ finishInstr t d iv st c, th.Rel m th' := by
  intro th' hth'
  have hc2 : c'.Rel m { c with prom := c'.prom.filter (· ≤ m) } :=
    ⟨hc.views.symm, rfl, hc.loadViews.symm, hc.succView.symm, hc.rmwWrote.symm, hc.stores.symm⟩
  have ht2 : t'.Rel m { t with prom := t'.prom.filter (· ≤ m) } :=
    ⟨h.st.symm, h.rview.symm, h.wview.symm, h.views.symm, rfl⟩
  obtain ⟨th0, hth0, hr⟩ := finishInstr_rel ht2 hc2 hiv.symm th' hth'
  change th0 ∈ finishInstr t d iv st { c with prom := c'.prom.filter (· ≤ m) } at hth0
  rw [finishInstr_withProm, List.mem_map] at hth0
  obtain ⟨th, hth, rfl⟩ := hth0
  refine ⟨th, hth, hr.st.symm, hr.rview.symm, hr.wview.symm, hr.views.symm, ?_⟩
  rw [(finishInstr_relKey hth').1, (finishInstr_relKey hth).1]
  exact hc.prom

/-- **The replay thread `t` against `mem` and the original thread `t'`
against `mem'`**: the thread-level form of `Ctx.RSim`. -/
structure _root_.Kraken.Promising.Thread.RSim (M : Memory) (tid : Nat) (w : Msg) (out : Bool) (t : Thread I)
    (mem : Memory) (t' : Thread I) (mem' : Memory) : Prop where
  ps : t.PSim M tid w out mem t' mem'
  ownP : ∀ u x, M.last < u → mem'.get? u = some x → u ≤ t'.views.getCoh x.loc
  xclP : ∀ a ν l, t'.views.xclb = some (a, ν, l) → M.last < a → a ≤ t'.views.getCoh l
  bndR : t.Bnd mem.last

/-- The initial contexts of an instruction of simulating threads. -/
theorem _root_.Kraken.Promising.Thread.RSim.ctx {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {t t' : Thread I}
    {mem mem' : Memory} (hs : t.RSim M tid w out mem t' mem') (log : List TraceEv) :
    Ctx.RSim M tid w out (out = false) { views := t.views, prom := t.prom, mem, log }
      { views := t'.views, prom := t'.prom, mem := mem', log } :=
  { ps := hs.ps.ctx log
    ownP := hs.ownP
    xclP := hs.xclP
    bndR := ⟨hs.bndR.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
    fresh := fun _ _ _ h => absurd h List.not_mem_nil }

/-- **The original's `coh w.loc` before its write of `w`**: an instruction
that writes `w` as "promise now" with a constraining view `ν ≤ |M|` starts
with `coh w.loc ≤ |M|`. -/
theorem stepOne_cohLe (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {M : Memory} {w : Msg} {ν : View} (hν : ν ≤ M.last)
    (hm : (w, ν) ∈ o.promisedNow) : t.views.getCoh w.loc ≤ M.last := by
  unfold stepOne at hstep
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
      obtain ⟨th, -, rfl⟩ := ho
      exact fut_back (runTree_pnD A tid _ tree _ st c2 hr) (fun _ _ h => absurd h List.not_mem_nil)
        (.inr ⟨ν, hν, hm⟩)

/-- **One instruction, replayed backwards.** An instruction of the original
thread is matched by an instruction of the replay thread, ending in
simulating threads. `hF`: while `w` is outstanding, the original's
instruction ends with `coh w.loc ≤ |M|` or writes `w` with a constraining
view `≤ |M|`; in the latter case phase A ends. -/
theorem stepOne_rsim (A : Arch) {M : Memory} {tid : Nat} {w : Msg} {out : Bool} {t t' : Thread I}
    {mem mem' : Memory} (hs : t.RSim M tid w out mem t' mem')
    {outs' : List (Except String (Outcome I))} (hstep' : stepOne A t' tid mem' = some outs')
    {o' : Outcome I} (ho' : .ok o' ∈ outs')
    (hF : out = true → o'.thread.views.getCoh w.loc ≤ M.last ∨ ∃ ν, ν ≤ M.last ∧ (w, ν) ∈ o'.promisedNow) :
    ∃ outs o out2, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧
      o.thread.RSim M tid w out2 o.mem o'.thread o'.mem ∧ (out = false → out2 = false) ∧
      ((∃ ν, ν ≤ M.last ∧ (w, ν) ∈ o'.promisedNow) → out2 = false) := by
  unfold stepOne at hstep' ⊢
  rw [hs.ps.rel.st]
  cases hex : I.exec t'.st with
  | none => rw [hex] at hstep'; cases hstep'
  | some tree =>
    rw [hex] at hstep'
    have hstep'' : _ = outs' := Option.some.inj hstep'
    subst hstep''
    rw [List.mem_flatMap] at ho'
    obtain ⟨r, hr', ho'⟩ := ho'
    cases r with
    | error m => simp at ho'
    | ok p =>
      obtain ⟨st, c2'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho'
      obtain ⟨th', hth', rfl⟩ := ho'
      obtain ⟨hp', hv'⟩ := finishInstr_relKey hth'
      have e1' := Views.getCoh_congr hv'
      have hiv := instrViews_rel hs.ps.rel (I.deps t'.st)
      have hivR := instrViews_le hs.bndR.regs (I.deps t'.st)
      have hiv' := instrViews_le hs.ps.bnd.regs (I.deps t'.st)
      have hc := hs.ctx [.instr tid (I.showInstr t'.st)]
      have hF' : out = true → FutOk M w c2' := by
        intro ho
        rcases hF ho with h | h
        · exact .inl (by rw [← e1']; exact h)
        · exact .inr h
      obtain ⟨c2, out2, hr, hs2, ho2⟩ := runTree_rsim A tid hiv tree out _ _ st c2' hc hivR hiv' hr' hF'
      obtain ⟨hcb, hl⟩ := runTree_bnd A tid _ tree _ st c2 hc.bndR hivR hr
      obtain ⟨hcb', hl'⟩ := runTree_bnd A tid _ tree _ st c2' hc.ps.bnd hiv' hr'
      obtain ⟨th, hth, hrel⟩ := finishInstr_rel_back hs.ps.rel hs2.ps.rel hiv th' hth'
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      refine ⟨_, _, out2, rfl, List.mem_flatMap.mpr ⟨.ok (st, c2), hr, List.mem_map.mpr ⟨th, hth, rfl⟩⟩,
        ?_, ho2, fun ⟨ν, hν, hm⟩ => ?_⟩
      · have e1 := Views.getCoh_congr hv
        have e2 := Views.getFwd_congr hv
        have e2' := Views.getFwd_congr hv'
        have ex' : th'.views.xclb = c2'.views.xclb := by
          have := congrArg Views.xclb hv'; simpa using this
        have hs2p := hs2.ps
        exact
          { ps :=
              { rel := hrel
                promEq := by rw [hp, hp']; exact hs2p.promEq
                promLe := by rw [hp']; exact hs2p.promLe
                memR := hs2p.memR
                memP := hs2p.memP
                outW := hs2p.outW
                tidR := hs2p.tidR
                tidP := hs2p.tidP
                ownR := fun u x h1 h2 hx => by rw [e1]; exact hs2p.ownR u x h1 h2 hx
                fwdR := fun l f h => by rw [e2] at h; exact hs2p.fwdR l f h
                fwdP := fun l f h => by rw [e2'] at h; exact hs2p.fwdP l f h
                lat := hs2p.lat
                bnd := finishInstr_bnd hcb'.views hcb'.loadViews hcb'.succView (hiv'.mono hl')
                  (hs.ps.bnd.regs.mono hl') th' hth' }
            ownP := fun u x h1 hx => by rw [e1']; exact hs2.ownP u x h1 hx
            xclP := fun a ν l hx hm => by rw [e1']; rw [ex'] at hx; exact hs2.xclP a ν l hx hm
            bndR := finishInstr_bnd hcb.views hcb.loadViews hcb.succView (hivR.mono hl)
              (hs.bndR.regs.mono hl) th hth }
      · cases out2
        · rfl
        · exact absurd hm (hs2.fresh rfl ν hν)

end Threads

end Kraken.Promising.Proj
