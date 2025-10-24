# Autonomous Learning Framework Usage Guide

## Overview

The LOGOS AGI Autonomous Learning Framework enables the system to continuously improve by analyzing evaluation failures, identifying reasoning gaps, and learning new IEL rules to address those gaps.

## Quick Start

### Running a Single Learning Cycle

```bash
# Run one learning cycle immediately
cd LOGOS_PXL_Core
python -m logos_core.logos_daemon --learn

# Run with custom configuration
python -m logos_core.logos_daemon --learn --learning-interval 6
```

### Continuous Learning Mode

```bash
# Enable continuous learning (checks every 3 hours by default)
python -m logos_core.logos_daemon --enable-learning

# Enable with custom interval (every 6 hours)
python -m logos_core.logos_daemon --enable-learning --learning-interval 6

# Background daemon with learning enabled
python -m logos_core.logos_daemon --daemon --enable-learning
```

## Architecture

The autonomous learning system consists of several components:

### Core Components

1. **TelemetryAnalyzer** (`logos_core/autonomous_learning.py`)
   - Parses telemetry data from evaluation failures
   - Identifies patterns in reasoning gaps
   - Groups similar failures for candidate generation

2. **LearningCycleManager** (`logos_core/autonomous_learning.py`)
   - Orchestrates the complete learning cycle
   - Manages rate limiting and safety constraints
   - Coordinates candidate generation, evaluation, and registration

3. **ReasoningGap** Data Structure
   - Represents identified gaps in reasoning capability
   - Includes severity, frequency, and context information
   - Used for candidate generation targeting

### Integration Points

- **IEL Generator** (`logos_core/meta_reasoning/iel_generator.py`)
  - Generates candidate IEL rules for identified gaps
  - Uses gap context to create targeted solutions

- **IEL Evaluator** (`logos_core/meta_reasoning/iel_evaluator.py`)
  - Evaluates candidate IEL rules for safety and effectiveness
  - Provides scores for candidate acceptance decisions

- **IEL Registry** (`logos_core/meta_reasoning/iel_registry.py`)
  - Stores successfully validated IEL rules
  - Manages rule metadata and versioning

## Learning Process

### 1. Gap Identification
- Analyzes telemetry data from `logs/monitor_telemetry.jsonl`
- Groups evaluation failures by error patterns
- Calculates gap severity based on frequency and impact
- Filters gaps using configurable thresholds

### 2. Candidate Generation
- For each significant reasoning gap:
  - Generates up to N candidate IEL rules (default: 5)
  - Uses gap context and failed propositions
  - Applies domain-specific generation strategies

### 3. Candidate Evaluation
- Each candidate undergoes comprehensive evaluation:
  - **Consistency**: Doesn't contradict existing rules
  - **Safety**: Preserves formal verification guarantees
  - **Performance**: Provides measurable improvement
  - **Overall Score**: Weighted combination of metrics

### 4. Registration and Integration
- Candidates exceeding threshold (default: 0.7) are registered
- Successful rules become available for reasoning
- Learning cycle results are logged for analysis

## Configuration

### Learning Configuration (`LearningConfig`)

```python
@dataclass
class LearningConfig:
    # Candidate generation
    max_candidates_per_gap: int = 5
    max_gaps_per_cycle: int = 10
    
    # Evaluation thresholds
    evaluation_threshold: float = 0.7
    min_gap_frequency: int = 3
    min_gap_severity: float = 0.3
    
    # Rate limiting
    max_cycles_per_hour: int = 3
    learning_history_days: int = 30
    
    # Integration
    telemetry_file: str = "logs/monitor_telemetry.jsonl"
    registry_path: str = "registry/iel_registry.db"
```

### Daemon Integration

```python
@dataclass
class DaemonConfig:
    # Learning settings
    enable_learning: bool = False
    learning_interval_hours: int = 3
    
    # Other daemon settings...
```

## Monitoring and Debugging

### Learning Status
```bash
# Check learning cycle history and statistics
python -c "
from logos_core.autonomous_learning import get_global_learning_manager
manager = get_global_learning_manager()
status = manager.get_learning_status()
print(f'Total cycles: {status[\"total_cycles\"]}')
print(f'Success rate: {status[\"average_acceptance_rate\"]:.2%}')
"
```

### Telemetry Analysis
```bash
# Analyze recent evaluation failures
python -c "
from logos_core.autonomous_learning import TelemetryAnalyzer, LearningConfig
analyzer = TelemetryAnalyzer('logs/monitor_telemetry.jsonl')
records = analyzer.load_telemetry()
print(f'Recent telemetry records: {len(records)}')

config = LearningConfig()
gaps = analyzer.identify_reasoning_gaps(records, config)
print(f'Identified gaps: {len(gaps)}')
for gap in gaps[:3]:
    print(f'  - {gap.domain}: {gap.description} (freq: {gap.frequency})')
"
```

### Registry Inspection
```bash
# List recently learned IEL rules
python -c "
from logos_core.meta_reasoning.iel_registry import IELRegistry
registry = IELRegistry('registry/iel_registry.db')
recent_rules = registry.list_candidates(limit=10, sort_by='created_at')
print(f'Recent IEL rules: {len(recent_rules)}')
for rule in recent_rules:
    print(f'  - {rule.rule_name}: {rule.domain} (score: {rule.confidence:.2f})')
"
```

## Testing

Run the comprehensive test suite:

```bash
cd LOGOS_PXL_Core
python tests/test_autonomous_learning.py
```

Test coverage includes:
- Telemetry analysis and gap identification
- Learning cycle execution with mocked components
- Error handling and edge cases
- Integration scenarios with real telemetry data

## Safety and Rate Limiting

### Safety Measures
- **Formal Verification Preservation**: New IEL rules cannot violate core axioms
- **Consistency Checking**: Candidates must be consistent with existing framework
- **Evaluation Thresholds**: Only high-quality candidates are accepted
- **Rollback Capability**: Failed rules can be removed from registry

### Rate Limiting
- Maximum 3 learning cycles per hour (configurable)
- Exponential backoff on consecutive failures
- Gap frequency thresholds prevent learning from isolated errors
- Learning history tracking prevents redundant cycles

## Troubleshooting

### Common Issues

1. **No gaps identified**
   - Check telemetry file exists: `logs/monitor_telemetry.jsonl`
   - Verify evaluation failures are being logged
   - Lower `min_gap_frequency` threshold

2. **Candidates not accepted**
   - Review evaluation threshold (`evaluation_threshold`)
   - Check candidate quality scores in learning logs
   - Verify IEL evaluator is working correctly

3. **Rate limiting active**
   - Wait for rate limit window to expire
   - Adjust `max_cycles_per_hour` if needed
   - Check learning cycle history for frequent failures

4. **Registry errors**
   - Ensure `registry/` directory exists
   - Check database permissions
   - Verify IEL registry schema is up to date

### Debug Logging

Enable detailed logging:

```python
import logging
logging.getLogger('logos_core.autonomous_learning').setLevel(logging.DEBUG)
```

## Performance Optimization

### Efficient Telemetry Analysis
- Telemetry files are processed incrementally
- Only recent failures (last 7 days) are analyzed by default
- Gap patterns are cached to avoid recomputation

### Candidate Generation Optimization
- Limit candidates per gap to prevent excessive evaluation
- Use domain-specific generation strategies
- Cache generation results for similar gaps

### Evaluation Efficiency
- Parallel candidate evaluation (when safe)
- Early termination for obviously poor candidates
- Incremental evaluation scores

## Integration with LOGOS AGI

The autonomous learning framework integrates seamlessly with the broader LOGOS AGI system:

- **Reference Monitor**: Provides telemetry data for gap identification
- **Proof Runtime Bridge**: Benefits from learned IEL rules for evaluation
- **Coherence Framework**: Validates consistency of new rules
- **Governance System**: Manages rule signing and authorization

This creates a closed-loop system where evaluation failures automatically drive improvement through autonomous learning.
