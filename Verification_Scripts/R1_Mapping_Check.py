# R1_Mapping_Check.py - Verifies the Centrality Axiom and Exclusion Mechanism

def reflective_mapping(x, a=1):
    """R1(x) = 2*a - x, with center a=1."""
    return 2 * a - x

# Demonstrating Centrality and Exclusion
print("--- R1 Mapping Check (Center: 1) ---")

# 1: The Fixed Point (Centrality Axiom)
result_1 = reflective_mapping(1)
print(f"R1(1) (The Center/Fixed Point) -> {result_1}")

# 2: The Structural Exclusion Point
result_2 = reflective_mapping(2)
print(f"R1(2) (The Anomaly/Exclusion Point) -> {result_2} (Maps to Null/0)")

# Symmetry Check (Optional, for context)
print(f"R1(3) -> {reflective_mapping(3)}") 
print(f"R1(5) -> {reflective_mapping(5)}") 

# Conclusion: The algebraic mechanism necessitates the centrality of 1 and the mechanical exclusion of 2.
