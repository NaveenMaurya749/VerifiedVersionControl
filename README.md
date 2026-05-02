# VerifiedVersionControl
Suppose a number of agents are collaborating on a repository located at `remote`, with access to 
a `local` repository each. How do we make sure that the changes contributed by multiple agents
do not affect each other's work, overwriting them?
We aimed to build a toy model of a version control system with verified behaviour
checked and enforced through Lean, to flag `merge` conflicts when they arise, and certify
whenever `actions` are safe.
We also implemented a `Diff-Tracker` along with a Json schema to implement the verifiction of 
incompatibility of commits.

## Documentation

Documentation for the project is available in either `V1_OVERVIEW.md` or `docs/V1_TECHNICAL_REPORT.pdf`.

## Origin

This project was built during the **LeanLang for Verified
Autonomy Hackathon** (April 17–18 + online through May 1,
2026) at the **Indian Institute of Science (IISc),
Bangalore**.
Sponsored by **[Emergence AI](https://www.emergence.ai)**
Organized by **[Emergence India Labs](https://east.emergence.ai)** in collaboration with
**IISc Bangalore**.

## Acknowledgments
This project was made possible by:
- **Emergence AI** — Hackathon sponsor
- **Emergence India Labs** — Event organizer and
research direction
- **Indian Institute of Science (IISc), Bangalore** —
Academic partner, hackathon co-design, tutorials,
and mentorship

## Links
- [Hackathon Page](https://east.emergence.ai/hackathon-april2026.html)
- [Emergence India Labs](https://east.emergence.ai)
- [Emergence AI](https://www.emergence.ai)
