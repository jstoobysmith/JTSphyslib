# AI policy

## 1. Introduction

1.1. Physlib generally welcomes AI-assisted contributions.

1.2. If you use an AI tool to help author a pull request to Physlib, you must follow the guidelines in this file.

1.3. Failure to follow these guidelines may result in your PR being closed without comment after a brief triage. Repeated failures may result in being banned from contributing to the project. This is to protect the project and the time of the maintainers.

1.4. Throughout this document, "must" denotes a hard requirement and "should" denotes a strong expectation that is not strictly enforced.

1.5. You must also follow any explicit instructions in [docs/ReviewGuidelines.md](docs/ReviewGuidelines.md).

1.6. These guidelines apply to any contribution where an AI tool produced more than trivial assistance.

1.7. The human author is fully responsible for every line of the PR.

## 2. Rules for the content of PRs

2.1. `theorem` must only be used for well-known results in the physics literature; otherwise `lemma` must be used.

2.2. Added results must be placed in sections with appropriate titles. Sections must be numbered using the scheme `# A. ...`, `## A.1. ...`, etc. See [Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean](Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean) for an example.

2.3. Results must be placed in the appropriate file, with the existing library structure in mind. Do not introduce new files without good reason.

2.4. Long proofs (over 50 LoC) should, where sensible, be split into smaller lemmas of general applicability.

2.5. New lemmas must not be trivial rewrites of existing lemmas in Mathlib or Physlib, unless they add new or different physics context.

2.6. All content must pass the linters described in [scripts/README.md](scripts/README.md).

2.7. Contributions must not contain `axiom` declarations. ch.

2.8. Any bibliographic references included must be verified by a human for correctness (existence of the work, accuracy of the cited statement, page numbers, etc.).

## 3. Rules for the structure of the PR

3.1. A pull request that adds new content (as opposed to refactoring existing content) should contain less than 250 lines of diff. Split larger contributions into multiple PRs.

3.2. PRs should be split into atomic commits where it makes sense.

3.3. Commit titles must describe the lemmas or definitions added or changed.

3.4. PRs must be focused and have well-defined scope.

## 4. Rules for the PR description

4.1. The PR description must list all lemmas and definitions added or removed, the file in which each appears, and a brief explanation of each.

4.2. The PR description should include a reviewer map: a brief guide indicating the order in which the reviewer should look at the changes.

4.3. The PR description should state the author's expertise in the area of the PR.

4.4. The PR description must disclose that an AI was used and describe the extent of its involvement.

4.5. The PR description must state whether a human has checked the correctness of any included references.

4.6. The PR must be concise.

## 5. Rules for the review process

5.1. All communication with human reviewers must be conducted by humans, not by an AI agent.

5.2. If an AI agent is used to implement reviewer feedback, the author must independently verify that the feedback has been addressed correctly before requesting re-review. This must not be left to the reviewer to check.
