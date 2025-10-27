import os

import requests
from fastapi import APIRouter

router2 = APIRouter()

ARCHON = os.getenv("ARCHON_URL", "http://archon:8000")
RABBIT = os.getenv("RABBIT_UI", "http://rabbitmq:15672")  # referential only


@router2.get("/gui/summary")
def summary():
    # placeholders; extend with real metrics collectors
    return {
        "services": {
            "archon": requests.get(f"{ARCHON}/health", timeout=3).json(),
        },
        "rabbitmq_ui": RABBIT,
    }
