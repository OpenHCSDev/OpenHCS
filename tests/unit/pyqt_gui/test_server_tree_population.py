from pyqt_reactive.services import DefaultServerInfoParser

from openhcs.pyqt_gui.widgets.shared.server_browser import ServerTreePopulation


class _FakeTree:
    def __init__(self):
        self.items = []

    def addTopLevelItem(self, item):
        self.items.append(item)


class _FakeProgressTracker:
    def __init__(self, execution_ids=None):
        self._execution_ids = execution_ids or []

    def get_execution_ids(self):
        return list(self._execution_ids)

    def get_events(self, execution_id):
        return []


def _execution_server_info():
    parser = DefaultServerInfoParser()
    return parser.parse(
        {
            "port": 7777,
            "ready": True,
            "server": "OpenHCSExecutionServer",
            "log_file_path": "/tmp/server.log",
            "workers": [],
            "running_executions": [],
            "queued_executions": [],
        }
    )


def test_server_tree_population_adds_scanned_servers():
    rendered = []
    populated = []
    tree = _FakeTree()

    population = ServerTreePopulation(
        create_tree_item=lambda display, status, info, data: {
            "display": display,
            "status": status,
            "info": info,
            "data": data,
            "children": [],
        },
        render_server=lambda info, status_icon: (
            rendered.append((info.port, status_icon)),
            {"port": info.port},
        )[1],
        populate_server_children=lambda info, item: (
            populated.append((info.port, item.get("port"))),
            False,
        )[1],
        server_info_parser=DefaultServerInfoParser(),
        ping_server=lambda _port: None,
        progress_tracker=_FakeProgressTracker(),
        ports_to_scan=[7777],
        last_known_servers={},
        log_info=lambda *_args, **_kwargs: None,
        log_debug=lambda *_args, **_kwargs: None,
    )
    population._get_launching_viewers = lambda: {}

    population.populate_tree(tree=tree, parsed_servers=[_execution_server_info()])

    assert len(tree.items) == 1
    assert rendered == [(7777, "✅")]
    assert populated == [(7777, 7777)]


def test_server_tree_population_adds_busy_execution_from_cache_when_progress_exists():
    tree = _FakeTree()

    class _ProgressTrackerWithEvents(_FakeProgressTracker):
        def __init__(self):
            super().__init__(execution_ids=["exec-1"])

        def get_events(self, execution_id):
            return [object()]

    cached_server = {
        "port": 7777,
        "ready": True,
        "server": "OpenHCSExecutionServer",
        "log_file_path": "/tmp/server.log",
        "workers": [],
        "running_executions": [],
        "queued_executions": [],
    }

    population = ServerTreePopulation(
        create_tree_item=lambda display, status, info, data: {
            "display": display,
            "status": status,
            "info": info,
            "data": data,
            "children": [],
        },
        render_server=lambda info, status_icon: {"port": info.port},
        populate_server_children=lambda info, item: False,
        server_info_parser=DefaultServerInfoParser(),
        ping_server=lambda _port: cached_server,
        progress_tracker=_ProgressTrackerWithEvents(),
        ports_to_scan=[7777],
        last_known_servers={7777: cached_server},
        log_info=lambda *_args, **_kwargs: None,
        log_debug=lambda *_args, **_kwargs: None,
    )
    population._get_launching_viewers = lambda: {}

    population.populate_tree(tree=tree, parsed_servers=[])

    assert len(tree.items) == 1
    assert tree.items[0]["status"] == "⚙️ Busy"
