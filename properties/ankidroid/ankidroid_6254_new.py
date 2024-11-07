import sys
sys.path.append("..")
from kea.main import *

class Test(Kea):
    

    @initialize()
    def set_up(self):
        d(text="Get Started").click()

    @main_path()
    def yue_should_display_in_language_mainpath(self):
        d(description="Navigate up").click()
        d(text="Settings").click()
        d(text="AnkiDroid").click()

    @precondition(
        lambda self: d(text="Language").exists() and
        d(text="Error reporting mode").exists()
    )
    @rule()
    def yue_should_display_in_language(self):
        d(text="Language").click()
        
        assert d(scrollable=True).scroll.to(text="粵語")
        




t = Test()

setting = Setting(
    apk_path="./apk/ankidroid/2.18alpha6.apk",
    device_serial="emulator-5554",
    output_dir="../output/ankidroid/6254/mutate_new",
    policy_name="random",
    
    number_of_events_that_restart_app = 100
)
start_kea(t,setting)

