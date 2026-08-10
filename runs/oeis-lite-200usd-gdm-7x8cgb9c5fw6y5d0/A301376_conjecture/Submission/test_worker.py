import sys
from parallel_search import worker, precompute_V
from multiprocessing import Event

shutdown_event = Event()
# Try running a tiny range to see if it crashes or completes normally
worker(0, 1500001, 1501000, shutdown_event)
print("Finished test worker successfully!")
