#!/usr/bin/env python3
"""
E2E Runtime Exercise: Gate a read-only tool through PolicyDemo.run equivalent.
Log proof token metadata: lemma-id, commit, coqchk stamp.
"""


# Simulate proof token metadata
class ProofToken:
    def __init__(self, lemma_id, commit, coqchk_stamp):
        self.lemma_id = lemma_id
        self.commit = commit
        self.coqchk_stamp = coqchk_stamp

# Simulate PolicyDemo.run
def policy_demo_run(token):
    print(f"Proof token metadata: lemma_id={token.lemma_id}, commit={token.commit}, coqchk_stamp={token.coqchk_stamp}")
    return True  # Allow

# Read-only tool
def read_only_tool():
    with open('README.md', encoding='utf-8') as f:
        content = f.read()[:100]  # Read first 100 chars
    print(f"Read-only tool executed: {content}")
    return content

# E2E demo
def e2e_demo():
    token = ProofToken("conservative_theorem", "b39a8d8", "coqchk_passed")
    if policy_demo_run(token):
        read_only_tool()
    else:
        print("Tool denied")

if __name__ == "__main__":
    e2e_demo()
