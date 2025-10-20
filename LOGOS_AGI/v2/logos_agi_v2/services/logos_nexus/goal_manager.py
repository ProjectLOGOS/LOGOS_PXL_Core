from datetime import datetime

class Goal:
    def __init__(self, name: str, priority: int = 10, source: str = "autonomous"):
        self.name = name
        self.priority = priority
        self.source = source
        self.created_at = datetime.utcnow()
        self.state = 'proposed'  # proposed, adopted, in_progress, shelved, retired

class GoalManager:
    def __init__(self):
        self.goals = []

    def propose_goal(self, name: str, priority: int = 10, source: str = "autonomous") -> Goal:
        goal = Goal(name, priority, source)
        self.goals.append(goal)
        print(f"[GoalManager] New Goal Proposed: '{name}'")
        return goal

    def adopt_goal(self, goal: Goal):
        if goal in self.goals and goal.state == 'proposed':
            goal.state = 'adopted'
            print(f"[GoalManager] Goal Adopted: '{goal.name}'")
        return goal
    
    def get_highest_priority_goal(self) -> Goal or None:
        adopted_goals = [g for g in self.goals if g.state == 'adopted']
        if not adopted_goals:
            return None
        return max(adopted_goals, key=lambda g: g.priority)