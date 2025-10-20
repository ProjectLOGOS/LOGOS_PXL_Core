# IMAE - Infinite Modal Analysis Engine
# Core system for seeding and tracing causal chains using Mandelbrot-Banach architecture

import math
import random

def is_prime(n):
    if n <= 1:
        return False
    if n <= 3:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

def goldbach_pair(n):
    if n <= 2 or n % 2 != 0:
        return None
    for i in range(2, n // 2 + 1):
        if is_prime(i) and is_prime(n - i):
            return (i, n - i)
    return None

def generate_mandelbrot_seed(real_base, imag_base, steps):
    c_values = []
    for i in range(steps):
        real = real_base + (i * 0.0001)
        imag = imag_base + (i * 0.0001)
        c_values.append(complex(real, imag))
    return c_values

def banach_node_trace(seed_number, depth):
    nodes = [seed_number]
    current = seed_number
    for _ in range(depth):
        if current % 2 == 0:
            pair = goldbach_pair(current)
            if pair:
                current = sum(pair)
            else:
                break
        else:
            current = current * 3 + 1  # Collatz-like behavior
        nodes.append(current)
    return nodes

def run_imae_test(seed_real=0.355, seed_imag=0.355, steps=10, depth=20):
    c_vals = generate_mandelbrot_seed(seed_real, seed_imag, steps)
    results = {}
    for idx, c in enumerate(c_vals):
        seed = int(abs(c.real * 1e5)) + int(abs(c.imag * 1e5))
        trace = banach_node_trace(seed, depth)
        results[f"Node_{idx}_Seed_{seed}"] = trace
    return results
