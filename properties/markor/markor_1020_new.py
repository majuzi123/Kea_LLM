from kea.core import *

class Test(Kea):
    

    @initializer()
    def set_up(self):
        d(resourceId="net.gsantner.markor:id/next").click()
        
        d(resourceId="net.gsantner.markor:id/next").click()
        
        d(resourceId="net.gsantner.markor:id/next").click()
        
        d(resourceId="net.gsantner.markor:id/next").click()
        
        d(text="DONE").click()
        
        
        if d(text="OK").exists():
            d(text="OK").click()

    @mainPath()
    def file_type_should_be_the_same_mainpath(self):
        d(resourceId="net.gsantner.markor:id/fab_add_new_item").click()
    
    @precondition(
        lambda self: d(resourceId="net.gsantner.markor:id/new_file_dialog__name").exists() 
        )
    @rule()
    def file_type_should_be_the_same(self):
        file_type = d(resourceId="net.gsantner.markor:id/new_file_dialog__type").child(className="android.widget.TextView").get_text()
        print("file_type: " + file_type)
        file_name_suffix = d(resourceId="net.gsantner.markor:id/new_file_dialog__ext").get_text()
        print("file_name_suffix: " + file_name_suffix)
        if file_type == "Markdown":
            assert file_name_suffix == ".md"
        elif file_type == "Plain Text":
            assert file_name_suffix == ".txt"
        elif file_type == "todo.txt":
            assert file_name_suffix == ".todo.txt"
        elif file_type == "AsciiDoc":
            assert file_name_suffix == ".adoc"
        elif file_type == "CSV":
            assert file_name_suffix == ".csv"
        elif file_type == "OrgMode":
            assert file_name_suffix == ".org"
        elif file_type == "Wikitext":
            assert file_name_suffix == ".txt"
        else:
            assert file_name_suffix == ".md"
        




if __name__ == "__main__":
    t = Test()
    
    setting = Setting(
        apk_path="./apk/markor/2.11.1.apk",
        device_serial="emulator-5554",
        output_dir="../output/markor/1020/guided_new",
        policy_name="guided"
    )
    start_kea(t,setting)
    
