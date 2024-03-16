import sys
from PyQt5.QtWidgets import QApplication, QWidget, QHBoxLayout, QVBoxLayout, QTextEdit, QPushButton, QMainWindow, QStatusBar
from PyQt5.QtGui import QIcon, QTextCharFormat, QFont, QSyntaxHighlighter, QTextDocument
from PyQt5.QtCore import Qt, QRegExp


class PythonHighlighter(QSyntaxHighlighter):
    def __init__(self, parent=None):
        super(QSyntaxHighlighter, self).__init__(parent)

        keywordFormat = QTextCharFormat()
        keywordFormat.setForeground(Qt.cyan)
        keywordFormat.setFontWeight(QFont.Bold)

        keywordPatterns = ["funcdef", "suchthat", "end", "let", "trycast", "on", "return", "typedef"]
        self.highlightingRules = [(QRegExp(pattern), keywordFormat)
                                   for pattern in keywordPatterns]

        symbolFormat = QTextCharFormat()
        symbolFormat.setForeground(Qt.cyan)
        symbolFormat.setFontWeight(QFont.Bold)

        symbolPatterns = ["\\+", "-", "/", "\\*", "->", "::", "\\(", "\\)"]
        self.highlightingRules.extend((QRegExp(pattern), symbolFormat)
                                      for pattern in symbolPatterns)

        self.commentFormat = QTextCharFormat()
        self.commentFormat.setForeground(Qt.darkGreen)
        self.commentStartExpression = QRegExp(r'\|\s*')
        self.commentEndExpression = QRegExp(r'\|')


    def highlightBlock(self, text):
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



class MyApp(QMainWindow):
    def __init__(self):
        super().__init__()

        self.initUI()

    def initUI(self):
        # Create central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)

        # Create text boxes
        self.left_textbox = QTextEdit()
        self.right_textbox = QTextEdit()

        # Create Python syntax highlighter
        self.highlighter = PythonHighlighter(self.left_textbox.document())

        # Create buttons with icons
        self.button1 = QPushButton(QIcon('icon1.png'), '')
        self.button2 = QPushButton(QIcon('icon2.png'), '')
        self.button3 = QPushButton(QIcon('icon3.png'), '')
        self.button4 = QPushButton(QIcon('icon4.png'), '')
        self.button5 = QPushButton(QIcon('icon5.png'), '')

        # Set fixed size for buttons to make them square
        button_size = 50  # Adjust the size as needed
        self.button1.setFixedSize(button_size, button_size)
        self.button2.setFixedSize(button_size, button_size)
        self.button3.setFixedSize(button_size, button_size)
        self.button4.setFixedSize(button_size, button_size)
        self.button5.setFixedSize(button_size, button_size)

        # Add buttons to top bar
        topbar_layout = QHBoxLayout()
        topbar_layout.addWidget(self.button1)
        topbar_layout.addWidget(self.button2)
        topbar_layout.addWidget(self.button3)
        topbar_layout.addWidget(self.button4)
        topbar_layout.addWidget(self.button5)

        # Set up layout
        vbox = QVBoxLayout(central_widget)
        vbox.addLayout(topbar_layout)  # Add buttons layout first
        hbox = QHBoxLayout()
        hbox.addWidget(self.left_textbox)
        hbox.addWidget(self.right_textbox)
        vbox.addLayout(hbox)  # Add text boxes layout next

        # Add status bar
        self.statusBar = QStatusBar()
        self.setStatusBar(self.statusBar)

        self.setWindowTitle('PyQt5 App')
        self.setGeometry(100, 100, 600, 400)
        self.show()


if __name__ == '__main__':
    app = QApplication(sys.argv)
    ex = MyApp()
    sys.exit(app.exec_())
