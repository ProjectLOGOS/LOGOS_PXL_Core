def obligation_for(action: str, state: str, props: str) -> str:
    return f"Good({action}) and TrueP({props}) and Coherent({state})"


def preserves_invariants(step: str) -> str:
    return f"preserves_invariants({step})"
