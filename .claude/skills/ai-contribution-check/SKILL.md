---
name: ai-contribution-check
description: Advisory AI check of a Physlib pull request, or of local changes, against the contribution tips in docs/ContributionTips/. Scores the change from 0 to 5 on each tip file with constructive suggestions; for a PR, posts one comment after the user confirms. Makes no decisions. Use when asked to check a PR or local changes against the contribution tips, to run the ai-contribution-check skill, or to work through PRs labelled `ai-contribution-check`.
argument-hint: "[PR number | local] [tip files…]"
---

This skill is model-independent and lives in `.agents/skills/ai-contribution-check/`.
Read `.agents/skills/ai-contribution-check/SKILL.md` and follow it, with `SKILL_DIR` being
`.agents/skills/ai-contribution-check`. The arguments, if any, are a PR number or `local`,
optionally followed by the names of the tip files to check: $ARGUMENTS
