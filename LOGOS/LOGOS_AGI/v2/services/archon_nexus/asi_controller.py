import logging
import asyncio


class ASILiftoffController:
    def __init__(self, logos_nexus_instance):
        self.logos_nexus = logos_nexus_instance
        self.desire_driver = logos_nexus_instance.desire_driver
        self.goal_manager = logos_nexus_instance.goal_manager
        self.self_improvement_manager = logos_nexus_instance.self_improvement_manager
        self.logger = logging.getLogger("ASI_CONTROLLER")
        self._is_running = False
        self._task = None

    async def start(self):
        self._is_running = True
        self._task = asyncio.create_task(self.run_liftoff_loop())
        self.logger.critical("ASI Liftoff Controller is ACTIVE.")

    def stop(self):
        self._is_running = False
        if self._task:
            self._task.cancel()
        self.logger.warning("ASI Liftoff Controller has been deactivated.")

    async def run_liftoff_loop(self):
        while self._is_running:
            self.logger.info("[ASI LOOP] Starting new cognitive cycle.")
            self.desire_driver.detect_gap(
                "SystemState", "Efficiency of causal simulation algorithm"
            )
            new_targets = self.desire_driver.get_new_targets()
            for target in new_targets:
                goal = self.goal_manager.propose_goal(name=target, priority=100)
                self.goal_manager.adopt_goal(goal)

            goal_to_execute = self.goal_manager.get_highest_priority_goal()
            if goal_to_execute and goal_to_execute.state == "adopted":
                self.logger.critical(f"[ASI LOOP] Pursuing meta-goal: {goal_to_execute.name}")
                goal_payload = {"goal_description": goal_to_execute.name}
                await self.logos_nexus.publish("archon_goals", goal_payload)
                goal_to_execute.state = "in_progress"

            await asyncio.sleep(30)  # Cognitive cycle
