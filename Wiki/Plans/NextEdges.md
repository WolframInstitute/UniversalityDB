# Plan: Next Edges to Formalize

## Goal

Decide which simulation proofs to formalize next after completing TM ↔ GS.

## Candidates

1. **Cocke-Minsky step simulation** (TM → 2-Tag): Currently a hypothesis. Would close the first link in the main universality chain. Hard — requires multi-phase binary tape encoding proof.

2. **Smith simulation** (CTS → (2,3) TM): Currently a hypothesis. Would close the last link. Very hard — 6-level hierarchy.

3. **Cook's Rule 110 universality** (CTS → ECA Rule 110): Glider collision encoding. Medium difficulty. Would add the ECA vertex properly.

4. **Neary-Woods polynomial chain** (TM → clockwise TM → CTS → Rule 110): Better overhead bounds. Multiple new vertices.

5. **Billiards** (Miranda-Ramos 2025): Continuous physical system. Novel vertex type. Proof may be hard to formalize.

## Steps

- [ ] Finish TM ↔ GS (prerequisite)
- [ ] Discuss priorities with human
- [ ] Pick next edge and create detailed plan

## History

| Date | Actor | Action |
|---|---|---|
| 2026-04-05 | LLM | Created plan from resource survey |
