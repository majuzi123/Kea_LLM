import sys
sys.path.append("..")
from kea.core import *

class Test(Kea):
    

    @initializer()
    def set_up(self):
        if d(text="OK").exists():
            d(text="OK").click()
            
        if d(text="Saved filters").exists():
            d.press("back")

    @mainPath()
    def save_reopen_task_should_not_change_number_mainpath(self):
        d(resourceId="nl.mpcjanssen.simpletask:id/fab").click()
        d(resourceId="nl.mpcjanssen.simpletask:id/taskText").set_text("Hello World!")
        d(resourceId="nl.mpcjanssen.simpletask:id/btnSave").click()

    @precondition(
        lambda self: int(d(resourceId="nl.mpcjanssen.simpletask:id/tasktext").count) > 0 and not d(text="Quick filter").exists() and not d(text="Settings").exists() and not d(text="Saved filters").exists())
    @rule()
    def save_reopen_task_should_not_change_number(self):
        task_count = int(d(resourceId="nl.mpcjanssen.simpletask:id/tasktext").count)
        print("task count: "+str(task_count))
        selected_task = random.randint(0, task_count - 1)
        print("selected task: "+str(selected_task))
        selected_task = d(resourceId="nl.mpcjanssen.simpletask:id/tasktext")[selected_task]
        selected_task_name = selected_task.get_text()
        print("selected task name: "+str(selected_task_name))
        selected_task.click()
        
        d(resourceId="nl.mpcjanssen.simpletask:id/update").click()
        
        d(resourceId="nl.mpcjanssen.simpletask:id/btnSave").click()
        
        new_count = int(d(resourceId="nl.mpcjanssen.simpletask:id/tasktext").count)
        print("new count: "+str(new_count))
        assert task_count == new_count, "task count should be the same"
    



if __name__ == "__main__":
    t = Test()
    
    setting = Setting(
        apk_path="./apk/simpletask/10.3.0.apk",
        device_serial="emulator-5554",
        output_dir="../output/simpletask/993/guided",
        policy_name="guided"
    )
    start_kea(t,setting)
    
