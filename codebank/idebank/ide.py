import sys
from PyQt5.QtWidgets import QApplication, QWidget, QHBoxLayout, QVBoxLayout, QTextEdit, QPushButton, QMainWindow, QStatusBar, QTextBrowser, QStackedWidget, QLabel, QMessageBox, QFileDialog
from PyQt5.QtGui import QIcon, QTextCharFormat, QFont, QSyntaxHighlighter, QTextDocument, QPixmap, QColor, QFont, QFontDatabase
from PyQt5.QtCore import Qt, QRegExp, QSize
import webbrowser
import subprocess
import time

class MPIRHighlighter(QSyntaxHighlighter):
    """
    Handle the formatting and display of MPIR syntax highlighting in code blocks.
    """

    def __init__(self, parent=None):
        """
        Initialise visual components of MPIR syntax highlighting.
        """
        super(QSyntaxHighlighter, self).__init__(parent)

        keywordFormat = QTextCharFormat()
        keywordFormat.setForeground(Qt.blue)
        keywordFormat.setFontWeight(QFont.Bold)

        keywordPatterns = ["funcdef", "suchthat", "end", "let", "trycast", "on", "return", "typedef", "into", "as", "set"]
        self.highlightingRules = [(QRegExp(pattern), keywordFormat)
                                   for pattern in keywordPatterns]

        symbolFormat = QTextCharFormat()
        purple_color = QColor(128, 0, 128)  # RGB values for purple
        symbolFormat.setForeground(purple_color)
        symbolFormat.setFontWeight(QFont.Bold)

        symbolPatterns = ["\\+", "-", "/", "\\*", "->", "::", "\\(", "\\)"]
        self.highlightingRules.extend((QRegExp(pattern), symbolFormat)
                                      for pattern in symbolPatterns)

        self.commentFormat = QTextCharFormat()
        self.commentFormat.setForeground(Qt.darkGreen)
        self.commentStartExpression = QRegExp(r'\|\s*')
        self.commentEndExpression = QRegExp(r'\|')


    def highlightBlock(self, text):
        """
        Handle display and formatting of MPIR syntax highlighted blocks.
        """
        for pattern, format in self.highlightingRules:
            expression = QRegExp(pattern)
            index = expression.indexIn(text)
            while index >= 0:
                length = expression.matchedLength()
                self.setFormat(index, length, format)
                index = expression.indexIn(text, index + length)

        self.setCurrentBlockState(0)

        startIndex = 0
        if self.previousBlockState() != 1:
            startIndex = self.commentStartExpression.indexIn(text)

        while startIndex >= 0:
            endIndex = self.commentEndExpression.indexIn(text, startIndex)
            if endIndex == -1:
                self.setCurrentBlockState(1)
                commentLength = len(text) - startIndex
            else:
                commentLength = endIndex - startIndex + self.commentEndExpression.matchedLength()

            self.setFormat(startIndex, commentLength, self.commentFormat)
            startIndex = self.commentStartExpression.indexIn(text, startIndex + commentLength)


class WikiPage(QWidget):
    def __init__(self) -> None:
        """
        Initialise and display the IDE's Wiki Page. Handle loading and unloading the content of the Wiki Page.
        """
        super().__init__()

        self.initUI()

    def initUI(self) -> None:
        """
        Initialise the contents of the Wiki Page. 
        """
        layout = QVBoxLayout()
        topbar_layout = QHBoxLayout()

        self.button1 = QPushButton()
        self.button2 = QPushButton()

        icon_size = QSize(40, 40)  # Adjust the size as needed
        self.button1.setIcon(QIcon(QPixmap('codebank/idebank/code.png').scaled(icon_size.width(), icon_size.height())))
        self.button1.setIconSize(icon_size)
        self.button2.setIcon(QIcon(QPixmap('codebank/idebank/github.png').scaled(icon_size.width(), icon_size.height())))
        self.button2.setIconSize(icon_size)

        button_size = 64  # Adjust the size as needed
        self.button1.setFixedSize(button_size, button_size)
        self.button2.setFixedSize(button_size, button_size)

        topbar_layout.addWidget(self.button1)
        topbar_layout.addStretch(1)
        topbar_layout.addWidget(self.button2)

        layout.addLayout(topbar_layout)

        # Create a QTextBrowser to display the HTML content
        self.text_browser = QTextBrowser()
        self.load_wiki_page()  # Load the wiki page content
        layout.addWidget(self.text_browser)

        # Create button to switch back to main page
        self.button1.clicked.connect(self.switch_to_main_page)
        self.button2.clicked.connect(lambda: webbrowser.open("https://www.github.com/tobybenjaminclark/mpir/wiki"))

        self.setLayout(layout)

    def load_wiki_page(self) -> None:
        """
        Load the HTML content of the Wiki Page from a file.
        """

        with open('codebank/idebank/wiki_page.html', 'r') as f:
            html_content = f.read()
        self.text_browser.setHtml(html_content)

    def switch_to_main_page(self)-> None:
        """
        Switch from the Wiki Page to the Main Page.
        """
        self.parent().switch_to_main_page()


class MyApp(QMainWindow):
    def __init__(self)-> None:
        """
        Initialise the PyQT5 window.
        """
        super().__init__()

        self.initUI()

    def initUI(self)-> None:
        """
        Initialise and display the contents of the UI.
        """

        # Create central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)

        self.filename = None
        self.config_file = None

        # Create the QTextEdit widget
        self.left_textbox = QTextEdit()
        self.right_textbox = QTextEdit()

        try:
            self.left_textbox.setFont(QFont("Monaco"))
            self.right_textbox.setFont(QFont("Monaco"))
        except:
            self.left_textbox.setFont(QFont("Courier New"))
            self.right_textbox.setFont(QFont("Courier New"))

        # Create Python syntax highlighter and associate it with the left_textbox
        self.highlighter = MPIRHighlighter(self.left_textbox.document())

        # Create buttons with icons
        self.button1 = QPushButton()
        self.button2 = QPushButton()
        self.button3 = QPushButton()
        self.button4 = QPushButton()
        self.button5 = QPushButton()
        self.button6 = QPushButton()
        self.button7 = QPushButton()
        self.button8 = QPushButton()

        # Set icons and adjust their size
        icon_size = QSize(40, 40)  # Adjust the size as needed
        self.button1.setIcon(QIcon(QPixmap('codebank/idebank/planet.png').scaled(icon_size.width(), icon_size.height())))
        self.button1.setIconSize(icon_size)
        self.button2.setIcon(QIcon(QPixmap('codebank/idebank/save.png').scaled(icon_size.width(), icon_size.height())))
        self.button2.setIconSize(icon_size)
        self.button3.setIcon(QIcon(QPixmap('codebank/idebank/folder.png').scaled(icon_size.width(), icon_size.height())))
        self.button3.setIconSize(icon_size)
        self.button4.setIcon(QIcon(QPixmap('codebank/idebank/python.png').scaled(icon_size.width(), icon_size.height())))
        self.button4.setIconSize(icon_size)
        self.button5.setIcon(QIcon(QPixmap('codebank/idebank/tex.png').scaled(icon_size.width(), icon_size.height())))
        self.button5.setIconSize(icon_size)
        self.button6.setIcon(QIcon(QPixmap('codebank/idebank/save_two.png').scaled(icon_size.width(), icon_size.height())))
        self.button6.setIconSize(icon_size)
        self.button7.setIcon(QIcon(QPixmap('codebank/idebank/config.png').scaled(icon_size.width(), icon_size.height())))
        self.button7.setIconSize(icon_size)
        self.button8.setIcon(QIcon(QPixmap('codebank/idebank/icon1.png').scaled(icon_size.width(), icon_size.height())))
        self.button8.setIconSize(icon_size)
        
        # Set fixed size for buttons to make them square
        button_size = 64  # Adjust the size as needed
        self.button1.setFixedSize(button_size, button_size)
        self.button2.setFixedSize(button_size, button_size)
        self.button3.setFixedSize(button_size, button_size)
        self.button4.setFixedSize(button_size, button_size)
        self.button5.setFixedSize(button_size, button_size)
        self.button6.setFixedSize(button_size, button_size)
        self.button7.setFixedSize(button_size, button_size)
        self.button8.setFixedSize(button_size, button_size)

        # Add buttons to top bar
        left_buttons_layout = QHBoxLayout()
        left_buttons_layout.addWidget(self.button1)
        left_buttons_layout.addWidget(self.button2)
        left_buttons_layout.addWidget(self.button3)

        right_buttons_layout = QHBoxLayout()
        right_buttons_layout.addWidget(self.button4)
        right_buttons_layout.addWidget(self.button5)
        right_buttons_layout.addWidget(self.button6)
        right_buttons_layout.addWidget(self.button7)
        right_buttons_layout.addWidget(self.button8)

        # Set up layout
        topbar_layout = QHBoxLayout()
        topbar_layout.addLayout(left_buttons_layout)
        topbar_layout.addStretch(1)  # Add stretchable space to push right-aligned buttons to the right
        topbar_layout.addLayout(right_buttons_layout)

        vbox = QVBoxLayout(central_widget)
        vbox.addLayout(topbar_layout)  # Add buttons layout first
        hbox = QHBoxLayout()
        hbox.addWidget(self.left_textbox)
        hbox.addWidget(self.right_textbox)
        vbox.addLayout(hbox)  # Add text boxes layout next

        # Create a stacked widget to switch between main page and wiki page
        self.stacked_widget = QStackedWidget()
        self.stacked_widget.switch_to_main_page = self.switch_to_main_page
        self.stacked_widget.addWidget(central_widget)  # Add main page
        self.wiki_page = WikiPage()
        self.stacked_widget.addWidget(self.wiki_page)  # Add wiki page

        # Add status bar
        self.statusBar = QStatusBar()
        self.setStatusBar(self.statusBar)

        # Add stacked widget to main window
        self.setCentralWidget(self.stacked_widget)

        self.setWindowTitle('Compiler')
        self.setGeometry(100, 100, 800, 600)
        self.show()

        # Connect button signals to slots
        self.button1.clicked.connect(self.switch_to_wiki_page)
        self.button4.clicked.connect(self.build_python)
        self.button5.clicked.connect(self.build_tex)
        self.button2.clicked.connect(self.save_text)
        self.button6.clicked.connect(self.save_output)
        self.button7.clicked.connect(self.load_config)
        self.button3.clicked.connect(self.load_text)

    def save_text(self)-> None:
        """
        Save the contents of the left textbox to a file, with the extention .mpir.
        """
        filename, _ = QFileDialog.getSaveFileName(self, "Save File", "", "MPIR files (*.mpir)")
        if filename:
            with open(filename, 'w') as f:
                self.filename = filename
                f.write(self.left_textbox.toPlainText().replace('\x00', ''))

    def save_output(self)-> None:
        """
        Save the contents of the right textbox to a file.
        """
        filename, _ = QFileDialog.getSaveFileName(self, "Save Output", "", "All Files (*)")
        if filename:
            with open(filename, 'w') as f:
                f.write(self.right_textbox.toPlainText())

    def load_text(self)-> None:
        """
        Prompt the user to select a file to open. Load the file contents into the left textbox.
        """
        filename, _ = QFileDialog.getOpenFileName(self, "Open File", "", "MPIR files (*.mpir)")
        if filename:
            with open(filename, 'r') as f:
                self.filename = filename
                self.left_textbox.setText(f.read())

    def load_config(self)-> None:
        """
        Prompt the user to select a file to open. Load the file contents into the right textbox.
        """
        filename, _ = QFileDialog.getOpenFileName(self, "Open File", "", "Config files (*.config)")
        if filename:
            with open(filename, 'r') as f:
                self.config_file = filename

    def switch_to_main_page(self)-> None:
        """
        Switch from alternate pages to the main page.
        """
        self.stacked_widget.setCurrentIndex(0)  # Index 0 is the main page

    def switch_to_wiki_page(self)-> None:
        """
        Switch from alternate pages to the wiki page.
        """
        self.stacked_widget.setCurrentIndex(1)  # Index 1 is the wiki page

    def build_python(self)-> None:
        """
        Build contents of a MPIR file to Python. Display the contents in the right textbox.
        """
        if self.filename is None:
            QMessageBox. critical(self, "Please Save File", "File has not been saved, to transpile please save.")
            return
        with open(self.filename, 'w') as f:
                f.write(self.left_textbox.toPlainText().replace('\x00', ''))

        command = f"./buildbank/mpir --i {self.filename} --o output.py --c config.json"
        print(command)

        process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        # Capture the output and wait for the process to finish

        # Read stdout and stderr line by line as they become available
        while True:
            stdout_line = process.stdout.readline()
            stderr_line = process.stderr.readline()
            
            if not stdout_line and not stderr_line:
                break
            
            if stdout_line:
                print(stdout_line.strip())
            if stderr_line:
                print(stderr_line.strip(), file=sys.stderr)

        time.sleep(0.2)
        
        try:
            with open("output.py", 'r') as f:
                self.right_textbox.setText(f.read())
        except:
            command = f"python3 codebank/modulebank/mpir_typechecker/typechecker.py --i temp_file.mpirast --o output.py --c config.json"
            print(command)

            process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            while True:
                stdout_line = process.stdout.readline()
                stderr_line = process.stderr.readline()
                
                if not stdout_line and not stderr_line:
                    break
                
                if stdout_line:
                    print(stdout_line.strip())
                if stderr_line:
                    print("ERROR: ", stderr_line.strip())
            
            time.sleep(0.2)

            with open("output.py", 'r') as f:
                self.right_textbox.setText(f.read())



    def build_tex(self)-> None:
        """
        Build a MPIR file to LaTeX. Display the result in the right textbox.
        """
        if self.filename is None:
            QMessageBox. critical(self, "Please Save File", "File has not been saved, to transpile please save.")
            return
        with open(self.filename, 'w') as f:
                f.write(self.left_textbox.toPlainText().replace('\x00', ''))

        command = f"./buildbank/mpir --i {self.filename} --o output.tex --c config.json"
        print(command)

        process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        # Capture the output and wait for the process to finish

        # Read stdout and stderr line by line as they become available
        while True:
            stdout_line = process.stdout.readline()
            stderr_line = process.stderr.readline()
            
            if not stdout_line and not stderr_line:
                break
            
            if stdout_line:
                print(stdout_line.strip())
            if stderr_line:
                print(stderr_line.strip(), file=sys.stderr)

        with open("output.tex", 'r') as f:
            self.right_textbox.setText(f.read())

    def build_pseudocode(self)-> None:
        self.right_textbox.setPlainText("pseudocode")

    def build_tests(self)-> None:
        self.right_textbox.setPlainText("tests")

if __name__ == '__main__':
    app = QApplication(sys.argv)
    ex = MyApp()
    sys.exit(app.exec_())
