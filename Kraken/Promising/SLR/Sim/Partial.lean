/-
Simulation library: the **partial-map** variant of `Sim.SimInv`, for a
per-thread replay in a target memory
that lacks one of the thread's own promises `p` (option (A) of general
`PromisePure`; see `KNOWN_GAPS.md` for why (A) itself stays open).

The map is `TMap.shiftAt p |M|` (`Sim/Maps.lean`), characterised abstractly
by `SimInvP.skip`/`SimInvP.shift`: `dom = [0, |M|] ∖ {p}`, `s ↦ s` below `p`,
`s ↦ s − 1` above it. The target memory is the source memory with `p`
deleted, so there are no foreign target messages (`NoForeign`) and
`|M'| + 1 = |M|`.

Unlike `SimInv`, the map is not total on the source memory (`domAll`) and not
total on the source promises (`p` is a promise outside the domain), so
`writeSuccs_sim` (which needs every promise in the domain and returns an
opaque `ρ'`) is not used for writes; the proofs below rebuild the write case
from the public pieces (`afterWrite_rel`, `CtxRel.fresh`, `atomic_sim`,
`freshMap_*`), dropping `p` from the promise relation around the fresh case.

- `SimInvP`: the invariant; `shiftAt_shape`: `shiftAt` has its shape.
- `SimInvP.read`: preservation through a read (the source never reads `p`).
- `SimInvP.write`: preservation through a write that does not fulfil `p`
  (fulfilling another promise, or fresh); the fresh case moves to
  `freshMap ρ`, again a shift map one longer.
- `SimInvP.brk`: the **break event**: the source write fulfils `p`; the
  target writes the same message fresh at its end (`writeSuccs_break`), and
  the result is `PostBreak`: the target memory is the source memory with `p`
  moved to the end, the promises relate under the same `ρ` (now total on the
  source promises), and the written message is identical. The monotone
  relation stops here.
-/
import Kraken.Promising.SLR.Sim.Instances

namespace Kraken.Promising

namespace Sim

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Promise lists without `p` -/

/-- Dropping a timestamp outside the domain from the source list. -/
theorem PromRel.erase_out {ρ : TMap} {p : Time} (hp : ¬ ρ.dom p) :
    ∀ {xs ys : List Time}, PromRel ρ xs ys → PromRel ρ (xs.erase p) ys
  | _, _, .nil => .nil
  | _, _, @PromRel.keep _ t xs ys ht h => by
    have hne : t ≠ p := fun e => hp (e ▸ ht)
    rw [List.erase_cons_tail (by simpa using hne)]
    exact .keep ht (PromRel.erase_out hp h)
  | _, _, @PromRel.drop _ t xs ys ht h => by
    by_cases e : t = p
    · subst e; rw [List.erase_cons_head]; exact h
    · rw [List.erase_cons_tail (by simpa using e)]
      exact .drop ht (PromRel.erase_out hp h)

/-- Adding back a timestamp outside the domain to the source list. -/
theorem PromRel.of_erase_out {ρ : TMap} {p : Time} (hp : ¬ ρ.dom p) :
    ∀ {xs ys : List Time}, PromRel ρ (xs.erase p) ys → PromRel ρ xs ys
  | [], _, h => by simpa using h
  | t :: xs, ys, h => by
    by_cases e : t = p
    · subst e; rw [List.erase_cons_head] at h; exact .drop hp h
    · rw [List.erase_cons_tail (by simpa using e)] at h
      cases h with
      | keep ht h' => exact .keep ht (PromRel.of_erase_out hp h')
      | drop ht h' => exact .drop ht (PromRel.of_erase_out hp h')

/-- Replace the source promise list of a relation. -/
theorem ctxRel_withProm {ρ : TMap} {c c' : Ctx} (h : CtxRel ρ c c') {xs : List Time}
    (hp : PromRel ρ xs c'.prom) : CtxRel ρ { c with prom := xs } c' :=
  ⟨h.mem, h.views, hp, h.loadViews, h.succView, h.rmwWrote, h.stores⟩

/-! ## The invariant -/

/-- **The partial-map invariant** of (A)'s per-thread replay (the variant of
`SimInv`): the relation; the source context bounded; the map a shift
map (`TMap.shiftAt`) at the erased promise `p` (`dom = [0, |M|] ∖ {p}`, shift by one above
`p`); `p` an outstanding promise of the source; every promise a message;
related instruction views; no foreign target message; the target memory one
message shorter. (`SimInv`'s `FgnSep`/`StaleFree` are not needed: the target
has *fewer* messages, `NoForeign`.) -/
structure SimInvP (ρ : TMap) (p : Time) (iv iv' : InstrViews) (c c' : Ctx) : Prop where
  rel : CtxRel ρ c c'
  bnd : c.Bnd
  skip : ∀ s, ρ.dom s ↔ s ≤ c.mem.last ∧ s ≠ p
  shift : ∀ s, ρ.dom s → ρ.f s = if s < p then s else s - 1
  pin : p ∈ c.prom
  ple : 1 ≤ p ∧ p ≤ c.mem.last
  promLe : ∀ s ∈ c.prom, s ≤ c.mem.last
  promNd : c.prom.Nodup
  ivr : IVLe ρ iv' iv
  ivb : iv.Le c.mem.last
  nofgn : NoForeign ρ c'.mem
  tlast : c'.mem.last + 1 = c.mem.last

variable (A : Arch) (tid : Nat)

theorem SimInvP.not_dom {ρ : TMap} {p : Time} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInvP ρ p iv iv' c c') :
    ¬ ρ.dom p := fun h => ((hs.skip p).mp h).2 rfl

/-- The initial instance: `TMap.shiftAt` satisfies the shape conditions. -/
theorem shiftAt_shape {p N : Time} (hp : 0 < p) :
    (∀ s, (TMap.shiftAt p N hp).dom s ↔ s ≤ N ∧ s ≠ p) ∧
      ∀ s, (TMap.shiftAt p N hp).dom s → (TMap.shiftAt p N hp).f s = if s < p then s else s - 1 :=
  ⟨fun _ => Iff.rfl, fun _ _ => rfl⟩

/-! ### Reads -/

/-- **A read** (never of `p`: `readSuccs` excludes the thread's own promises)
is matched by the target read of the image timestamp; `SimInvP` holds after
it. -/
theorem SimInvP.read {ρ : TMap} {p : Time} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInvP ρ p iv iv' c c')
    {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val} {c₁ : Ctx}
    (hx : (t, v, c₁) ∈ readSuccs A iv c k xcl l noRet) :
    ∃ c₁', (ρ.f t, v, c₁') ∈ readSuccs A iv' c' k xcl l noRet ∧ SimInvP ρ p iv iv' c₁ c₁' ∧ c₁.mem = c.mem := by
  obtain ⟨hb1, ht, hm⟩ := readSuccs_bnd A iv hs.bnd hs.ivb hx
  obtain ⟨t0, v0, he, -, -, -, hpc⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, -, -⟩ := he
  subst h1
  have htp : t ≠ p := by
    rintro rfl
    rw [List.contains_iff_mem.mpr hs.pin] at hpc; cases hpc
  have hd : ρ.dom t := (hs.skip t).mpr ⟨ht, htp⟩
  obtain ⟨c₁', hx', hr⟩ := readSuccs_sim A hs.rel hs.ivr hx hd (NoForeign.gap hs.nofgn l _ _)
  have hm' : c₁'.mem = c'.mem := by
    obtain ⟨_, _, he, -⟩ := (mem_readSuccs A).mp hx'
    simp only [Prod.mk.injEq] at he
    rw [he.2.2]; rfl
  have hp : c₁.prom = c.prom := by
    obtain ⟨_, _, he, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at he
    rw [he.2.2]; rfl
  refine ⟨c₁', hx', ⟨hr, hb1, hm ▸ hs.skip, hs.shift, hp ▸ hs.pin, hm ▸ hs.ple, ?_, hp ▸ hs.promNd, hs.ivr,
    hm ▸ hs.ivb, hm' ▸ hs.nofgn, by rw [hm', hm]; exact hs.tlast⟩, hm⟩
  rw [hp, hm]; exact hs.promLe

/-! ### Writes that do not fulfil `p` -/

private theorem le_fv_max' {ρ : TMap} {a' a b' b : View} (ha : a' ≤ ρ.fv a) (hb : b' ≤ ρ.fv b) :
    max a' b' ≤ ρ.fv (max a b) := by
  rw [ρ.fv_max]; omega_t

/-- **A write that does not fulfil `p`** (it fulfils another promise, or it
is fresh) is matched by the target write at the image timestamp (a fresh
target write at `|M'| + 1 = |M|` for a fresh source write at `|M| + 1`), and
`SimInvP` holds after it, for the same map or for `freshMap ρ` (the shift map
one longer). -/
theorem SimInvP.write {ρ : TMap} {p : Time} {iv iv' ivs ivs' : InstrViews} {c c' : Ctx}
    (hs : SimInvP ρ p iv iv' c c') (hivs : IVLe ρ ivs' ivs) (hivsb : ivs.Le c.mem.last)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr tr' : Option Time} (htr : TrRel ρ tr tr')
    {extra extra' : View} (hex : extra' ≤ ρ.fv extra) (hexb : extra ≤ c.mem.last)
    {xr xr' : View} (hxr : xr' ≤ ρ.fv xr) (hxrb : xr ≤ c.mem.last)
    {c₂ : Ctx} (h : c₂ ∈ writeSuccs A tid ivs c k xcl l v tr extra xr) (hnb : p ∈ c₂.prom) :
    ∃ ρ' : TMap, ∃ c₂', c₂' ∈ writeSuccs A tid ivs' c' k xcl l v tr' extra' xr' ∧ SimInvP ρ' p iv iv' c₂ c₂' ∧
      Ext ρ ρ' c.mem.last ∧ c.mem.last ≤ c₂.mem.last := by
  have hc := hs.rel
  have hpre := writePre_le A hivs hc.views k hex
  have hB : max (writePre A ivs' c' k extra') (c'.views.getCoh l) ≤
      ρ.fv (max (writePre A ivs c k extra) (c.views.getCoh l)) := le_fv_max' hpre (hc.views.coh l)
  have hfwd : max ivs'.addrR (max ivs'.dataR extra') ≤ ρ.fv (max ivs.addrR (max ivs.dataR extra)) :=
    le_fv_max' hivs.addrR (le_fv_max' hivs.dataR hex)
  have hgap : ∀ a, AtomGap ρ c'.mem l tid a (c'.mem.last + 1) := fun a => NoForeign.atom hs.nofgn l tid _ _
  obtain ⟨hb2, hm⟩ := writeSuccs_bnd A tid ivs hs.bnd hivsb hexb h
  -- the exclusive part of `WriteOk`, transported
  have hatom : ∀ (t t' : Time), (∀ s, ρ.dom s → ρ.f s < t' → s < t) → t' ≤ c'.mem.last + 1 →
      (∀ a, ρ.dom a → a < t → ρ.f a < t') →
      (∀ a, tr = some a → a < t ∧ c.mem.atomic l tid a t = true) →
      ∀ a', tr' = some a' → a' < t' ∧ c'.mem.atomic l tid a' t' = true := by
    intro t t' htt ht' hlt hok a' ha'
    cases tr with
    | none => cases tr' with
      | none => cases ha'
      | some _ => exact htr.elim
    | some a =>
      cases tr' with
      | none => cases ha'
      | some b =>
        cases ha'
        obtain ⟨hd, rfl⟩ := htr
        obtain ⟨h1, h2⟩ := hok a rfl
        refine ⟨hlt a hd h1, atomic_sim tid hc.mem hd h2 htt ?_⟩
        intro s' w x y z u
        exact hgap _ s' w x (Nat.lt_of_lt_of_le y ht') z u
  rcases (mem_writeSuccs A tid).mp h with ⟨t, htp, w, hw, hl, hv, htid, ⟨hok1, hok2⟩, rfl⟩ | ⟨⟨hok1, hok2⟩, rfl⟩
  · -- fulfil a promise `t ≠ p` (in the domain)
    have htnp : t ≠ p := by
      rintro rfl
      exact (List.Nodup.not_mem_erase hs.promNd) hnb
    have ht : ρ.dom t := (hs.skip t).mpr ⟨hs.promLe t htp, htnp⟩
    refine ⟨ρ, _, (mem_writeSuccs A tid).mpr (.inl ⟨ρ.f t, (hc.prom.mem _).mpr ⟨t, htp, ht, rfl⟩, w,
      by rw [hc.mem.get t ht]; exact hw, hl, hv, htid, ⟨Nat.lt_of_le_of_lt hB (fv_lt_f ht hok1), ?_⟩, rfl⟩), ?_,
      Ext.refl _ _, hm⟩
    · exact hatom t (ρ.f t) (fun s hs' h => (ρ.f_lt_iff hs' ht).mp h)
        (Nat.le_succ_of_le (hc.mem.f_le t ht)) (fun a ha h => ρ.strict a t ha ht h) hok2
    · refine ⟨afterWrite_rel A hc hivs.addrW _ xcl l v ht hfwd true true hxr, hb2, hs.skip, hs.shift, hnb, hs.ple, ?_,
        hs.promNd.erase t, hs.ivr, hs.ivb, hs.nofgn, hs.tlast⟩
      intro s hs'
      exact hs.promLe s (List.mem_of_mem_erase hs')
  · -- a fresh write at the end of both memories
    have hnd := hs.not_dom
    have hpd : ∀ s ∈ (c.prom.erase p), ρ.dom s := by
      intro s hs'
      refine (hs.skip s).mpr ⟨hs.promLe s (List.mem_of_mem_erase hs'), ?_⟩
      rintro rfl
      exact (List.Nodup.not_mem_erase hs.promNd) hs'
    have hcm : CtxRel ρ { c with prom := c.prom.erase p } c' := ctxRel_withProm hc (PromRel.erase_out hnd hc.prom)
    have hlast0 : c'.mem.last + 1 = c.mem.last := hs.tlast
    have hbm : Ctx.Bnd { c with prom := c.prom.erase p } := ⟨hs.bnd.views, hs.bnd.loadViews, hs.bnd.succView⟩
    have hc2m := CtxRel.fresh hcm hbm hpd { loc := l, val := v, tid }
      (pn := c.promisedNow ++ [({ loc := l, val := v, tid }, max (writePre A ivs c k extra) (c.views.getCoh l))])
      (pn' := c'.promisedNow ++ [({ loc := l, val := v, tid }, max (writePre A ivs' c' k extra') (c'.views.getCoh l))])
    have hn := freshMap_new hcm.mem
    have hnd' : ¬ (freshMap ρ hcm.mem).dom p := by
      rintro (h | h)
      · exact hnd h
      · have := hs.ple.2; omega_t
    -- put `p` back into the source promises
    have hc2 : CtxRel (freshMap ρ hcm.mem)
        { c with mem := (c.mem.append { loc := l, val := v, tid }).1, prom := c.prom ++ [c.mem.last + 1],
                 promisedNow := c.promisedNow ++
                   [({ loc := l, val := v, tid }, max (writePre A ivs c k extra) (c.views.getCoh l))] }
        { c' with mem := (c'.mem.append { loc := l, val := v, tid }).1, prom := c'.prom ++ [c'.mem.last + 1],
                  promisedNow := c'.promisedNow ++
                    [({ loc := l, val := v, tid }, max (writePre A ivs' c' k extra') (c'.views.getCoh l))] } := by
      refine ctxRel_withProm hc2m (PromRel.of_erase_out hnd' ?_)
      rw [List.erase_append_left _ hs.pin]
      exact hc2m.prom
    have hiv2 : ivs'.addrW ≤ (freshMap ρ hcm.mem).fv ivs.addrW := by
      rw [freshMap_fv hcm.mem hivsb.addrW]; exact hivs.addrW
    have hfwd2 : max ivs'.addrR (max ivs'.dataR extra') ≤
        (freshMap ρ hcm.mem).fv (max ivs.addrR (max ivs.dataR extra)) := by
      rw [freshMap_fv hcm.mem (by have := hivsb.addrR; have := hivsb.dataR; omega_t)]; exact hfwd
    have hr := afterWrite_rel A hc2 hiv2 (A.storeKind k) xcl l v hn.1 hfwd2 false false
      (xr := xr) (xr' := xr') (by rw [freshMap_fv hcm.mem hxrb]; exact hxr)
    rw [hn.2] at hr
    have hlast := Memory.last_append c.mem { loc := l, val := v, tid }
    have hlast' := Memory.last_append c'.mem { loc := l, val := v, tid }
    refine ⟨freshMap ρ hcm.mem, _, (mem_writeSuccs A tid).mpr (.inr ⟨⟨?_, ?_⟩, rfl⟩),
      ⟨hr, hb2, fun s => ?_, fun s hs' => ?_, ?_, ?_, ?_, ?_, hs.ivr.lift hs.ivb (fun x hx => freshMap_fv hcm.mem hx),
        hs.ivb.mono hm, ?_, ?_⟩, ⟨freshMap_agree hcm.mem, fun x hx => freshMap_fv hcm.mem hx⟩, hm⟩
    · exact Nat.lt_succ_of_le (Nat.le_trans hB (fv_le_last hc.mem _))
    · exact hatom (c.mem.last + 1) (c'.mem.last + 1) (fun s hs' _ => Nat.lt_succ_of_le (hc.mem.dom_le s hs'))
        (Nat.le_refl _) (fun a ha _ => Nat.lt_succ_of_le (hc.mem.f_le a ha)) hok2
    · -- the domain: one longer
      show (ρ.dom s ∨ s = c.mem.last + 1) ↔ s ≤ (afterWrite A ivs _ _ _ _ _ _ _ _ xr).mem.last ∧ s ≠ p
      change _ ↔ s ≤ (c.mem.append _).1.last ∧ s ≠ p
      rw [hlast, hs.skip s]
      have := hs.ple.2
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨Nat.le_succ_of_le h1, h2⟩
        · exact ⟨Nat.le_refl _, by omega_t⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_eq_of_le h1 with h1 | h1
        · exact .inl ⟨Nat.le_of_lt_succ h1, h2⟩
        · exact .inr h1
    · -- the shift
      rcases hs' with hs' | rfl
      · rw [(freshMap_agree hcm.mem s hs').2]; exact hs.shift s hs'
      · rw [hn.2]
        have := hs.ple.2
        have hlt : ¬ (c.mem.last + 1 < p) := by omega_t
        simp only [hlt, ↓reduceIte]; omega_t
    · -- `p` is still outstanding
      show p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      have := hs.ple.2
      exact (List.mem_erase_of_ne (by omega_t)).mpr (List.mem_append_left _ hs.pin)
    · show 1 ≤ p ∧ p ≤ (c.mem.append _).1.last
      rw [hlast]; exact ⟨hs.ple.1, Nat.le_succ_of_le hs.ple.2⟩
    · intro s hs'
      change s ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) at hs'
      change s ≤ (c.mem.append _).1.last
      rw [hlast]
      rcases List.mem_append.mp (List.mem_of_mem_erase hs') with h1 | h1
      · exact Nat.le_succ_of_le (hs.promLe s h1)
      · rw [List.mem_singleton.mp h1]; exact Nat.le_refl _
    · show ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).Nodup
      have hni : c.mem.last + 1 ∉ c.prom := fun h' => by have := hs.promLe _ h'; omega_t
      rw [List.erase_append_right _ hni, List.erase_cons_head, List.append_nil]
      exact hs.promNd
    · -- no foreign target message
      intro s' h1 h2
      show ∃ s, (freshMap ρ hcm.mem).dom s ∧ (freshMap ρ hcm.mem).f s = s'
      change s' ≤ (c'.mem.append _).1.last at h2
      rw [hlast'] at h2
      rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
      · obtain ⟨s, hs', rfl⟩ := hs.nofgn s' h1 (Nat.le_of_lt_succ h2)
        exact ⟨s, (freshMap_agree hcm.mem s hs').1, (freshMap_agree hcm.mem s hs').2⟩
      · exact ⟨_, hn.1, hn.2⟩
    · show (c'.mem.append _).1.last + 1 = (c.mem.append _).1.last
      rw [hlast, hlast', hlast0]

/-! ### The break event -/

/-- **After the break**: the source fulfilled `p` (at `p`), the target wrote
the same message fresh at its end `|M'| + 1 = |M|`. The target memory is the
source memory with `p` moved to the end (`mem` for the other messages,
`moved` for `p`), both one message long more than before on the target side
(`tlast`); the promises relate under the same `ρ`, now with every source
promise in the domain; the written message is identical (same location,
value and thread). Views are not related: the target's coherence view of
the location is `|M|`, the source's `p` (the map would have to send `p` to
`|M|`, above the images of larger timestamps: not monotone). -/
structure PostBreak (ρ : TMap) (p : Time) (c₂ c₂' : Ctx) : Prop where
  mem : MemRel ρ c₂.mem c₂'.mem
  moved : c₂'.mem.get? c₂'.mem.last = c₂.mem.get? p
  tlast : c₂'.mem.last = c₂.mem.last
  prom : PromRel ρ c₂.prom c₂'.prom
  promDom : ∀ s ∈ c₂.prom, ρ.dom s

/-- **The break event.** The source write fulfils `p`. The target performs
the same write, of the same effective kind, fresh at its end
(`writeSuccs_break`), given the target's exclusive check up to its end
(vacuous for a plain store, `tr = none`). After it, `PostBreak`. -/
theorem SimInvP.brk {ρ : TMap} {p : Time} {iv iv' ivs ivs' : InstrViews} {c c' : Ctx}
    (hs : SimInvP ρ p iv iv' c c') (hivs : IVLe ρ ivs' ivs)
    {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr tr' : Option Time} (htr : TrRel ρ tr tr')
    {extra extra' : View} (hex : extra' ≤ ρ.fv extra)
    (hatomT : ∀ a, tr' = some a → c'.mem.atomic l tid a (c'.mem.last + 1) = true)
    {c₂ : Ctx} (h : c₂ ∈ writeSuccs A tid ivs c k xcl l v tr extra) (hb : p ∉ c₂.prom) :
    ∃ c₂', c₂' ∈ writeSuccs A tid ivs' c' k xcl l v tr' extra' ∧ PostBreak ρ p c₂ c₂' ∧
      c₂'.mem = (c'.mem.append { loc := l, val := v, tid }).1 ∧
      c₂.mem.get? p = some { loc := l, val := v, tid } := by
  have hc := hs.rel
  have hlast' := Memory.last_append c'.mem { loc := l, val := v, tid }
  rcases (mem_writeSuccs A tid).mp h with ⟨t, htp, w, hw, hl, hv, htid, -, rfl⟩ | ⟨-, rfl⟩
  rotate_left
  · -- a fresh source write keeps `p` outstanding: not a break
    exfalso; apply hb
    show p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
    have := hs.ple.2
    exact (List.mem_erase_of_ne (by omega_t)).mpr (List.mem_append_left _ hs.pin)
  -- the fulfilled promise is `p`
  have htp' : t = p := by
    refine Classical.byContradiction fun hne => hb ?_
    exact (List.mem_erase_of_ne (Ne.symm hne)).mpr hs.pin
  subst htp'
  have hwm : w = { loc := l, val := v, tid } := by cases w; simp only at hl hv htid; subst hl hv htid; rfl
  subst hwm
  refine ⟨_, writeSuccs_break A tid hc hivs k xcl l v htr hex hatomT, ?_, rfl, hw⟩
  refine ⟨⟨hc.mem.init, hc.mem.dom_le, fun s hs' => ?_, fun s hs' => ?_⟩, ?_, ?_, ?_, ?_⟩
  · show ρ.f s ≤ (c'.mem.append _).1.last
    rw [hlast']; exact Nat.le_succ_of_le (hc.mem.f_le s hs')
  · show (c'.mem.append _).1.get? (ρ.f s) = c.mem.get? s
    rw [Memory.get?_append_of_le _ _ _ (hc.mem.f_le s hs'), hc.mem.get s hs']
  · show (c'.mem.append _).1.get? (c'.mem.append _).1.last = c.mem.get? t
    rw [hlast', Memory.get?_append_last, hw]
  · show (c'.mem.append _).1.last = c.mem.last
    rw [hlast']; exact hs.tlast
  · show PromRel ρ (c.prom.erase t) ((c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1))
    have hni : c'.mem.last + 1 ∉ c'.prom := by
      intro h'
      obtain ⟨s, hs1, hs2, hs3⟩ := (hc.prom.mem _).mp h'
      have := hc.mem.f_le s hs2; omega_t
    rw [List.erase_append_right _ hni, List.erase_cons_head, List.append_nil]
    exact PromRel.erase_out hs.not_dom hc.prom
  · intro s hs'
    refine (hs.skip s).mpr ⟨hs.promLe s (List.mem_of_mem_erase hs'), ?_⟩
    rintro rfl
    exact (List.Nodup.not_mem_erase hs.promNd) hs'

end Sim

end Kraken.Promising
