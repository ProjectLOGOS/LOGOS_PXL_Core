def person_relation(operation: str, agent_a: str, agent_b: str) -> str or bool:
    """
    Models the group-theoretic person relation based on divine processions.
    F∘S=H (Father operating on Son yields Spirit)
    S∘H=F (Son operating on Spirit yields Father)
    H∘F=S (Spirit operating on Father yields Son)
    """
    a, b = agent_a[0].upper(), agent_b[0].upper()

    if operation == "compose":
        if (a, b) == ("F", "S"): return "H"
        if (a, b) == ("S", "H"): return "F"
        if (a, b) == ("H", "F"): return "S"
        if (a, b) == ("S", "F"): return "H"  # Simplified for commutativity in this model

    if operation == "verify_closure":
        return (person_relation("compose", "F", "S") == "H" and
                person_relation("compose", "S", "H") == "F" and
                person_relation("compose", "H", "F") == "S")

    return False
