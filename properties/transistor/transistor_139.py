import sys
sys.path.append("..")
from kea.core import *

class Test(Kea):
    

    @initializer()
    def set_up(self):
        d(description="Add").click()
        
        d(className="android.widget.EditText").set_text("http://st01.dlf.de/dlf/01/128/mp3/stream.mp3")
        
        d(text="ADD").click()
        
        d(description="Add").click()
        
        d(className="android.widget.EditText").set_text("http://stream.live.vc.bbcmedia.co.uk/bbc_world_service")
        
        d(text="ADD").click()
        
        d(description="Add").click()
        
        d(className="android.widget.EditText").set_text("http://www.101smoothjazz.com/101-smoothjazz.m3u")
        
        d(text="ADD").click()

    @mainPath()
    def duplicate_playback_indicator_shouldnot_appear_mainapth(self):
        d(resourceId="org.y20k.transistor:id/list_item_textview").click()

    @precondition(
        lambda self: d(resourceId="org.y20k.transistor:id/list_item_playback_indicator").exists()
    )
    @rule()
    def duplicate_playback_indicator_shouldnot_appear(self):
        assert int(d(resourceId="org.y20k.transistor:id/list_item_playback_indicator").count) == 1




if __name__ == "__main__":
    t = Test()
    
    setting = Setting(
        apk_path="./apk/transistor/2.1.5.apk",
        device_serial="emulator-5554",
        output_dir="../output/transistor/139/guided",
        policy_name="guided"
    )
    start_kea(t,setting)
    
