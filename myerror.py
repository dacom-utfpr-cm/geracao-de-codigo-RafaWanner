import configparser
import inspect

import sys

config = None

class MyError():

  def __init__(self, et):
    self.config = configparser.RawConfigParser()
    self.config.read('ErrorMessages.properties')
    self.errorType = et

  def newError(self, flag, key, line=None, column=None, **data):
    message = ''
    if(key):
      if(flag):
        message = key
      
      else:
        error = self.config.get(self.errorType, key)
        if(line and column):
          message = f"Error[{line}][{column}]:" + error
        else:
          message = error
          
    if(data):
      if(not flag):
        for key, value in data.items():
          message = f"Error[{line}][{column}]:" + message + ", " f"{key}: {value}"

    return(message)
    #frame = inspect.stack()[1][0]

    #print(inspect.getframeinfo(frame).__getitem__(0))
    #print(inspect.getframeinfo(frame).__getitem__(1))


# le = MyError('LexerErrors')

# print(le.newError('ERR-LEX-001'))