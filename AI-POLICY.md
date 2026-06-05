# AI Policy for Physlib

We welcome AI-generated contributions to this repository. However, we have expectations for their use, which are detailed in this file. Please read this carefully; if you are using an AI agent, ensure it also reads this policy.

We apply one-look triage to AI-generated PRs. This means that if we suspect a PR is AI-generated, we will look it once, and if it clearly does not meet our standards, we will close it without comment. If it does meet our standards, we will proceed with the normal review process.

## Types of PRs

Within Physlib there are two types of PRs:

- *Type 1*: PRs where being wrong is short-lived and low cost. Examples include: improving formatting, adding infrastructure for interacting with the library, golfing a proof, adding a TODO item, adding informal lemmas or definitions, and adding files for organization.

- *Type 2*: PRs where being wrong is long-lived and high cost. This primarily includes PRs that add new lemmas, definitions, or proofs — since these add maintenance burden and can affect downstream results. It also includes PRs that add critical meta-programs or scripts.

We accept AI-generated content of both types. However, for Type 2 PRs we expect the author to take full responsibility for the content; in particular, they must be a domain expert.

## Standards for AI-generated pull-requests

Because AI agents make it easy to produce content quickly, we hold AI-generated PRs to a higher standard then human PRs. In practice, AI-generated PRs often impose more of a review burden on maintainers than human-authored ones, and we expect authors to compensate for this upfront.

In the following, "must" denotes a hard requirement, while "should" denotes a strong expectation that we are not strict about.

- You must follow any explicit instructions given in [./docs/ReviewGuidelines.md](./docs/ReviewGuidelines.md).
- Added code must follow the style conventions of Mathlib.
- The PR must be split into small commits. Commits should build, and must have descriptive titles.
- Added results (Type 2 PR) must be placed in the appropriate file with library structure in mind.
- Added results (Type 2 PR) must not duplicate any lemma already in Physlib or Mathlib, nor should be a trivial restatement of an existing one.
- Documentation must follow the example in [./Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean](./Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean).
- The PR description must list all lemmas and definitions added or removed, the file they appear in, and a brief explanation of each.
- The PR description must disclose that an AI was used and describe the extent of its involvement.
- For Type 2 PRs, the description should include a statement of the author's expertise in the relevant domain.
- Long proofs should be decomposed into smaller lemmas.
- The review process involves back-and-forth with reviewers. All communication with humans must be conducted by humans, not by an AI agent.
- If an AI agent is used to implement reviewer feedback, the author must verify that the feedback has been addressed correctly. This must not be left to the reviewer to check.
- PRs should be kept to a manageable size. If a PR is too large, it should be split into multiple smaller ones.
- Any references included in the PR must be verified by a human for correctness, and this verification must be declared in the PR description.
- Authors should include a reviewer map in the PR description: a brief guide indicating the order in which the reviewer should look at the changes.
- The PR must pass the linters described in [./scripts/README.md](./scripts/README.md).
