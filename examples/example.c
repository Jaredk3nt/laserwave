#include <ncurses.h>
/**
 * TO-DO NEXT:
 * validation layers
 */

App app;
App* Engine = &app;

const uint32_t WIDTH = 800U;
const uint32_t HEIGHT = 600U;

const char *validationLayers[1] = {
	"VK_LAYER_KHRONOS_validation"
};
const bool enableValidationLayers = false;

void run() {
        initWindow();
        initVulkan();
        mainLoop();
        cleanup();
}

void initWindow() {
        glfwInit();

	if (!glfwVulkanSupported()) {
		printf("[ERROR] Vulkan is not available\n");
	}

        glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
        glfwWindowHint(GLFW_RESIZABLE, GLFW_FALSE);

        Engine->window = glfwCreateWindow(WIDTH, HEIGHT, "Tetris", NULL, NULL);
}

void initVulkan() {
        createInstance();
	selectPhysicalDevice();
	createLogicalDevice();
	//dDisplayEngineProperties();
}


void selectPhysicalDevice() {
	// Instead of checking for suitability of devices, 
	// consider scoring them and picking the best one 
	Engine->physicalDevice = VK_NULL_HANDLE;

	uint32_t deviceCount = 0;
	vkEnumeratePhysicalDevices(Engine->instance, &deviceCount, NULL);
	//printf("Device count: %d\n", deviceCount);

	if (deviceCount == 0) {
		printf("[ERROR] Failed to find physical devices with vulkan support\n");
	}

	VkPhysicalDevice devices[deviceCount];
	vkEnumeratePhysicalDevices(Engine->instance, &deviceCount, devices);

	uint32_t cnt = 0;
	for (VkPhysicalDevice *device = &devices[0]; cnt < deviceCount; cnt++) {
		if (isDeviceSuitable(device)) {
			Engine->physicalDevice = *device;
			break;
		}
		device = devices + 1;
	}
}



void print_in_middle(WINDOW *win, int starty, int startx, int width, char *string);
int main(int argc, char *argv[])
{	initscr();			/* Start curses mode 		*/
	if(has_colors() == FALSE)
	{	endwin();
		printf("Your terminal does not support color\n");
		exit(1);
	}
	start_color();			/* Start color 			*/
	init_pair(1, COLOR_RED, COLOR_BLACK);

	attron(COLOR_PAIR(1));
	print_in_middle(stdscr, LINES / 2, 0, 0, "Viola !!! In color ...");
	attroff(COLOR_PAIR(1));
    	getch();
	endwin();
}
void print_in_middle(WINDOW *win, int starty, int startx, int width, char *string)
{	int length, x, y;
	float temp;

	if(win == NULL)
		win = stdscr;
	getyx(win, y, x);
	if(startx != 0)
		x = startx;
	if(starty != 0)
		y = starty;
	if(width == 0)
		width = 80;

	length = strlen(string);
	temp = (width - length)/ 2;
	x = startx + (int)temp;
	mvwprintw(win, y, x, "%s", string);
	refresh();
}