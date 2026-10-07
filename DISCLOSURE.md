# Disclosure

JD Jones directed this project. Claude (Anthropic) was used throughout: the theorems and their proofs, the
searches, the checkers and the repository were produced in that process, and the repository was written by
Claude, with one exception. The statement of the dimension theorem (theorem 12) and an outline of its proof
were proposed by a GPT model (OpenAI), consulted by the author on the eleven-theorem version of the repository
(commit `3348ece`); that model also found two inaccurate sentences in the documentation. The outline was
audited and the Lean proof of the theorem written with Claude. The ten definitions are restated from OpenAI's
openai/math (Apache-2.0; see NOTICE), and a few lemmas adapt proofs from the same tree, as their docstrings
say. Verification status is stated in VERIFICATION.md. No independent human review or source-author
endorsement is claimed.
