def before_scenario(context, scenario):
    context.app = None
    context.initiator = None
    context.sender = "INITIATOR"
    context.target = "ACCEPTOR"


def after_scenario(context, scenario):
    if context.initiator is not None:
        context.initiator.stop()
